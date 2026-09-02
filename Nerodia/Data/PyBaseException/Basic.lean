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
/-- Returns whether {lean}`self` is an instance of {lit}`BaseException`. -/
@[extern "nerodia_py_object_is_base_exception_instance"]
def PyObject.isBaseExceptionInstance (self : @& PyObject) : Bool :=
  self ⦂ baseException

open PyObject in
public instance : DecidablePy baseException := private_decl%
  (Internal.decPy isBaseExceptionInstance (by simp [isBaseExceptionInstance]))
