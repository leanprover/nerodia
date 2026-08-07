/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Lean
public import Lean.Elab.Command
public import Lean.DocString.Extension
public meta import Nerodia.Compiler.Meta.PyName
public meta import Nerodia.Compiler.Meta.Extension

/-! # Nerodiac Commands -/

open Lean Elab Command

namespace Nerodia.Compiler

/--
Declares this Lean module to define a Python module with the specified name.

A docstring will be used as the {lit}`__doc__` attribute of the Python module.
-/
syntax (name := pyModuleCmd) (docComment)? "py_module " str : command

@[command_elab pyModuleCmd]
public meta def elabPyModuleCmd : CommandElab := fun stx => do
  let `(command| $[$doc?]? py_module%$tk $name) := stx
    | throwError "ill-formed `py_module` syntax"
  withRef tk do
  let name ← mkPyModName name
  let doc? ← doc?.mapM fun doc => do
    return doc.getDocString.removeLeadingSpaces.trimAscii.copy
  if hasModuleConfig (← getEnv) then
    throwError "A Python module has already been configured."
  modifyEnv fun env => modCfgExt.setState env (some {name, doc?})
