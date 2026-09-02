/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO

namespace Nerodia

open Classical in
/-- Returns whether {lean}`self` is an instance of {lit}`types.ModuleType`. -/
@[extern "nerodia_py_object_is_module_instance"]
def PyObject.isModuleInstance (self : @& PyObject) : Bool :=
  self ⦂ moduleType

open PyObject in
public instance : DecidablePy moduleType := private_decl%
  (Internal.decPy isModuleInstance (by simp [isModuleInstance]))

/--
Imports the module named {lean}`modName`.

In Python, the import can be anything, so this may not return a {lean}`PyModule`.
-/
@[extern "nerodia_import"]
public opaque «import» (modName : @& String) : CPyIO PyObject

namespace PyModule

/-- Adds an object {lean}`val` to the module {lean}`self` as {lean}`name`. -/
@[extern "nerodia_py_module_add_by_string"]
public opaque addByString (name : @& String) (val : @& PyObject)
  (self : @& PyModule) : CPyUnitIO
