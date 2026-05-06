/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Lean.Data.Json
import Lean.Environment
import Lean.Compiler.NameMangling
import Nerodia.Compiler.ModuleConfig.Extension
-- needed due to how Lake links executables (TODO: fix)
import Nerodia.InitFlag

open System (FilePath)
open Lean (Json ToJson FromJson toJson fromJson?)

namespace Nerodia

structure Member where
  name : String
  ty : String
  doc? : Option String

structure Module where
  name : String
  leanInit : String
  leanModule : Lean.Name
  doc? : Option String := none
  inits : Array String := #[]
  attrs : Array AttrDef := #[]
  methods : Array MethodDef := #[]

def writeCFile (path : FilePath) (mod : Module) : IO Unit := do
  let c ← IO.FS.Handle.mk path .write
  c.putStr "\
    // Nerodia compiler output\n\
    #include <Python.h>\n\
    #include <lean/lean.h>\n"
  -- Module initialization
  c.putStr "\nvoid nerodia_initialize_lean(void);"
  c.putStr "\nvoid nerodia_mark_end_initialization(void);"
  c.putStr "\nvoid nerodia_set_init_error(lean_obj_arg init_res, const char *mod_name);"
  c.putStr s!"\nlean_obj_res {mod.leanInit}(uint8_t builtin);"
  for fn in mod.inits do
    c.putStr s!"\nint32_t {fn}(size_t m);"
  let lb := "{"
  c.putStr s!"\n\
    \nstatic int module_exec(PyObject *m) {lb}\
    \n  nerodia_initialize_lean();\
    \n  lean_object* res = {mod.leanInit}(true);\
    \n  nerodia_mark_end_initialization();\
    \n  if (lean_io_result_is_error(res)) {lb}\
    \n    nerodia_set_init_error(res, {mod.leanModule.toString.quote});\
    \n    return -1;\
    \n  }\
    \n  lean_dec_ref(res);"
  if h : mod.inits.size = 1 then
    c.putStr s!"\n  return {mod.inits[0]}((size_t)m);"
  else
    for fn in mod.inits do
      c.putStr s!"\n  if ({fn}((size_t)m) != 0) return -1;"
    c.putStr "\n  return 0;"
  c.putStr "\n}\n"
  c.putStr "\
    \nstatic PyModuleDef_Slot module_slots[] = {\
    \n  {Py_mod_exec, module_exec},\
    \n  {0, NULL}\
    \n};\n"
  -- Module methods
  for m in mod.methods do
    c.putStr "\n"
    c.putStr m.cSig
    c.putStr ";"
  c.putStr "\n\nstatic PyMethodDef module_methods[] = {"
  for m in mod.methods do
    c.putStr s!"\
      \n \{\
      \n    .ml_name = {m.name.quote},\
      \n    .ml_meth = (PyCFunction){m.cSym},\
      \n    .ml_flags = {m.flags},\
      \n    .ml_doc = {m.doc?.elim "NULL" (·.quote)},\
      \n  },"
  c.putStr "\
    \n {NULL, NULL, 0, NULL}\
    \n};\n"
  -- Module definition
  c.putStr s!"\
    \nstatic PyModuleDef module = {lb}\
    \n  .m_base = PyModuleDef_HEAD_INIT,\
    \n  .m_name = \"{mod.name}._lean\",\
    \n  .m_size = 0,\
    \n  .m_methods = module_methods,\
    \n  .m_slots = module_slots,\
    \n  .m_doc = {mod.doc?.elim "NULL" (·.quote)},\
    \n};\n"
  c.putStr "\
    \nPyMODINIT_FUNC PyInit__lean(void) {\
    \n  return PyModuleDef_Init(&module);\
    \n}\n"

def writePyiFile (path : FilePath) (mod : Module) : IO Unit := do
  let pyi ← IO.FS.Handle.mk path .write
  pyi.putStr "# Nerodia compiler output\n"
  if let some doc := mod.doc? then
    pyi.putStr doc.quote
    pyi.putStr "\n"
  for m in mod.attrs do
    pyi.putStr s!"\n{m.name}: {m.ty}"
    if let some doc := m.doc? then
      pyi.putStr "\n"
      pyi.putStr doc.quote
  pyi.putStr "\n"
  for m in mod.methods do
    pyi.putStr "\ndef "
    pyi.putStr m.name
    pyi.putStr m.pySig
    if let some doc := m.doc? then
      pyi.putStr ":\n  "
      pyi.putStr doc.quote
      pyi.putStr "\n  ..."
    else
      pyi.putStr ": ..."
  pyi.putStr "\n"

structure CompilerConfig where
  leanModule : Lean.Name
  cFile : FilePath
  pyiFile : FilePath
  deriving ToJson, FromJson

end Nerodia

open Nerodia

public def main (args : List String) : IO UInt32 := do
  let [arg] := args
    | IO.eprintln "USAGE: nerodiac <config.json>"
      return 1
  let contents ← IO.FS.readFile arg
  let cfg ←
    match Json.parse contents >>= fromJson? with
    | .ok (cfg : CompilerConfig) => pure cfg
    | .error e =>
      IO.eprintln s!"invalid configuration: {e}"
      return 1
  unsafe Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[cfg.leanModule] .empty
    (leakEnv := true) (loadExts := true)
  let modIdx := env.getModuleIdx? cfg.leanModule |>.get!
  let some modCfg := modCfgExt.getStateByIdx? env modIdx |>.join
    | IO.eprintln "module lacks a Nerodia configuration"
      return 1
  let mod : Module := {
    name := modCfg.name
    doc? := modCfg.doc?
    inits := modCfg.inits
    leanInit := Lean.mkModuleInitializationFunctionName cfg.leanModule (env.getModulePackageByIdx? modIdx)
    leanModule := cfg.leanModule
    attrs := modCfg.attrs
    methods := modCfg.methods
  }
  writeCFile cfg.cFile mod
  writePyiFile cfg.pyiFile mod
  return 0
