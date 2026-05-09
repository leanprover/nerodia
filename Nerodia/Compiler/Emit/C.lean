/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Compiler.ModuleConfig.Basic

open System (FilePath)

namespace Nerodia

public def writeCFile (path : FilePath) (mod : ModuleDef) : IO Unit := do
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
  for a in mod.attrs do
    c.putStr s!"\nsize_t {a.cSym}(void);"
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
  for a in mod.attrs do
    c.putStr s!"\n  if (PyModule_Add(m, {a.name.quote}, (PyObject*){a.cSym}()) != 0) return -1;"
  for fn in mod.inits do
    c.putStr s!"\n  if ({fn}((size_t)m) != 0) return -1;"
  c.putStr "\
    \n  return 0;\
    \n}\n"
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
