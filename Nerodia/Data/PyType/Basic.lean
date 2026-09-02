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
/-- Returns whether {lean}`self` is an instance of {lit}`type`. -/
@[extern "nerodia_py_object_is_type_instance"]
def PyObject.isTypeInstance (self : @& PyObject) : Bool :=
  self ⦂ type

open PyObject in
public instance : DecidablePy type := private_decl%
  (Internal.decPy isTypeInstance (by simp [isTypeInstance]))

namespace PyType

/-- Returns the qualified name of the type. -/
@[extern "nerodia_py_type_get_qual_name"]
public opaque getQualName (self : @& PyType) : CPyIO PyStr
