/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Compiler.Data.ModuleConfig.Basic

open System (FilePath)

namespace Nerodia.Compiler

/--
Converts a string to its representation as a C string literal.

Similar to Lean's private {lit}`Lean.Compiler.LCNF.EmitC.quoteString`, this
parallels {name}`String.quote`, but produces C syntax rather than Lean syntax.
Control characters are escaped as 3-digit octals: a C hex escape is unbounded,
so the literal {lit}`"\x0beta"` is a single, out-of-range escape, whereas an
octal consumes 3 digits.

Non-ASCII bytes are escaped as well, keeping the literal pure ASCII.
A narrow string literal is decoded from the compiler's source character set
and re-encoded into its execution character set. The C standard fixes neither.
An octal escape denotes a byte value directly, so it passes through both
conversions unchanged.
-/
public def cstr (s : String) : String :=
  s.toUTF8.foldl (init := "\"") (· ++ escape ·) ++ "\""
where
  escape (b : UInt8) : String :=
    if b == '\n'.toUInt8 then "\\n"
    else if b == '\r'.toUInt8 then "\\r"
    else if b == '\t'.toUInt8 then "\\t"
    else if b == '\"'.toUInt8 then "\\\""
    else if b == '\\'.toUInt8 then "\\\\"
    else if b == '?'.toUInt8 then "\\?" -- Avoids trigraphs (removed in C23)
    else if ' '.toUInt8 ≤ b ∧ b ≤ '~'.toUInt8 then String.singleton (Char.ofNat b.toNat)
    else
      let n := b.toNat
      String.ofList ['\\', octDigit (n / 64), octDigit (n / 8 % 8), octDigit (n % 8)]
  octDigit (n : Nat) : Char :=
    Char.ofNat ('0'.toNat + n)

public def writeCFile (path : FilePath) (mod : ModuleDef) : IO Unit := do
  let c ← IO.FS.Handle.mk path .write
  c.putStr "\
    // Nerodia compiler output\n\
    #include <Python.h>\n\
    #include <lean/lean.h>\n"
  -- Module initialization
  c.putStr "\nbool nerodia_initialize_lean(const char *mod_name);"
  c.putStr "\nbool nerodia_mark_end_initialization(lean_obj_arg res);"
  c.putStr s!"\nlean_obj_res {mod.leanInit}(uint8_t builtin);"
  for a in mod.attrs do
    c.putStr s!"\nsize_t {a.cSym}(void);"
  for fn in mod.inits do
    c.putStr s!"\nint32_t {fn}(size_t m);"
  let lb := "{"
  c.putStr s!"\n\
    \nstatic int module_exec(PyObject *m) {lb}\
    \n  if (!nerodia_initialize_lean({cstr mod.leanModule.toString})) return -1;\
    \n  if (!nerodia_mark_end_initialization({mod.leanInit}(true))) return -1;"
  for a in mod.attrs do
    c.putStr s!"\n  if (PyModule_Add(m, {cstr a.name}, (PyObject*){a.cSym}()) != 0) return -1;"
  for fn in mod.inits do
    c.putStr s!"\n  if ({fn}((size_t)m) != 0) return -1;"
  c.putStr "\
    \n  return 0;\
    \n}\n"
  -- Free-threading and multiple interpreters are not currently supported.
  c.putStr "\
    \nstatic PyModuleDef_Slot module_slots[] = {\
    \n  {Py_mod_exec, module_exec},\
    \n  {Py_mod_multiple_interpreters, Py_MOD_MULTIPLE_INTERPRETERS_NOT_SUPPORTED},\
    \n  {Py_mod_gil, Py_MOD_GIL_USED},\
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
      \n    .ml_name = {cstr m.name},\
      \n    .ml_meth = (PyCFunction){m.cSym},\
      \n    .ml_flags = {m.flags},\
      \n    .ml_doc = {m.doc?.elim "NULL" cstr},\
      \n  },"
  c.putStr "\
    \n {NULL, NULL, 0, NULL}\
    \n};\n"
  -- Module definition
  c.putStr s!"\
    \nstatic PyModuleDef module = {lb}\
    \n  .m_base = PyModuleDef_HEAD_INIT,\
    \n  .m_name = {cstr s!"{mod.name}._lean"},\
    \n  .m_size = 0,\
    \n  .m_methods = module_methods,\
    \n  .m_slots = module_slots,\
    \n  .m_doc = {mod.doc?.elim "NULL" cstr},\
    \n};\n"
  c.putStr "\
    \nPyMODINIT_FUNC PyInit__lean(void) {\
    \n  return PyModuleDef_Init(&module);\
    \n}\n"
