/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO
meta import Nerodia.Internal.ViewMethod

/-! # Python Booleans -/

namespace Nerodia

/-! ## True -/

open Classical in
@[extern "nerodia_py_object_is_true"]
def PyObject.isTrue (self : @& PyObject) : Bool :=
  self ⦂ true

open PyObject in
public instance : DecidablePy true := private_decl%
  (Internal.decPy isTrue fun _ => by simp [PyObject.isTrue])

open Internal Nerodia in
/-- Returns a reference to the {lit}`True` constant. -/
@[extern "nerodia_py_environment_true"]
public def PyEnvironment.true (env : @& PyEnvironment) : PyTrue :=
  env.trueCore

/-- Returns the {lit}`True` constant of the Python environment. -/
@[extern "nerodia_get_py_true"]
public def getPyTrue : CPyBaseIO PyTrue :=
  PyBaseIO.toCPyBaseIO do (·.true) <$> getPyEnvironment

/-! ## False -/

open Classical in
@[extern "nerodia_py_object_is_false"]
def PyObject.isFalse (self : @& PyObject) : Bool :=
  self ⦂ false

open PyObject in
public instance : DecidablePy false := private_decl%
  (Internal.decPy isFalse fun _ => by simp [PyObject.isFalse])

open Internal Nerodia in
/-- Returns a reference to the {lit}`False` constant. -/
@[extern "nerodia_py_environment_false"]
public def PyEnvironment.false (env : @& PyEnvironment) : PyFalse :=
  env.falseCore

/-- Returns the {lit}`False` constant of the Python environment. -/
@[extern "nerodia_get_py_false"]
public def getPyFalse : CPyBaseIO PyFalse :=
  PyBaseIO.toCPyBaseIO do (·.false) <$> getPyEnvironment

/-! ## bool -/

open Classical in
@[extern "nerodia_py_object_is_bool_instance"]
def PyObject.isBoolInstance (self : @& PyObject) : Bool :=
  self ⦂ bool

open PyObject in
public instance : DecidablePy bool := private_decl%
  (Internal.decPy isBoolInstance fun _ => by simp [PyObject.isBoolInstance])

/-- Returns the Python boolean corresponding to the Lean boolean {lean}`b`. -/
@[inline] public def mkPyBool (b : Bool) : CPyBaseIO PyBool :=
  bif b then getPyTrue.promote else getPyFalse.promote

/-- Returns the boolean value of {lean}`self` as a Lean {lean}`Bool`. -/
@[inline, view_method] public def PyBool.toBool (self : PyBool) : Bool :=
  self ⦂ true
