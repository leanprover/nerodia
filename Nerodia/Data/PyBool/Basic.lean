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

/-! ## Bool View -/

/-- Equips {lean}`α` with the dot notation methods of a {lean}`PyObject`. -/
public abbrev PyBoolView (α : Type u) := α

/-! ## True -/

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.true : TypeExpr :=
  ⟨"Literal[True]"⟩

public instance : CoeDep Bool true TypeExpr := ⟨.true⟩

noncomputable opaque PyEnvironment.trueAddr (env : PyEnvironment) : Addr

open Internal in
noncomputable def PyEnvironment.trueRaw (env : @& PyEnvironment) : Py.Raw :=
  .ofModel {env, addr := env.trueAddr, kind := .int, hint := .true}

open Internal in
public protected def Typing.true : Typing :=
  ofFn fun o => o.toModel.toInnerModel = o.toModel.env.trueRaw.toModel.toInnerModel

public instance : CoeDep Bool true Typing := ⟨.true⟩
public instance : ToTypeExpr true := ⟨true⟩

theorem PyEnvironment.trueRaw_hasType {env} : trueRaw env ⦂ true := by
  simp [PyEnvironment.trueRaw, Typing.true]

open PyEnvironment in
public instance : NonemptyPy true :=
  .intro (trueRaw Classical.ofNonempty) trueRaw_hasType

/-- A Python {lit}`True` constant. -/
public abbrev PyTrue := PyBoolView <| PyObjectView <| Py true

public instance : ViewPy true PyTrue := ⟨rfl⟩

open Classical in
@[extern "nerodia_py_object_is_true"]
def PyObject.isTrue (self : @& PyObject) : Bool :=
  self ⦂ true

open PyObject in
public instance : DecidablePy true := private_decl%
  (Internal.decPy isTrue fun _ => by simp [PyObject.isTrue])

/-- Returns a reference to the {lit}`True` constant. -/
@[extern "nerodia_py_environment_true"]
public def PyEnvironment.true (env : @& PyEnvironment) : PyTrue :=
  ⟨env.trueRaw, trueRaw_hasType⟩

/-- Returns the {lit}`True` constant of the Python environment. -/
@[extern "nerodia_get_py_true"]
public def getPyTrue : CPyBaseIO PyTrue :=
  PyBaseIO.toCPyBaseIO do (·.true) <$> getPyEnvironment

/-! ## False -/

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.false : TypeExpr :=
  ⟨"Literal[False]"⟩

public instance : CoeDep Bool false TypeExpr := ⟨.false⟩

noncomputable opaque PyEnvironment.falseAddr (env : PyEnvironment) : Addr

open Internal in
noncomputable def PyEnvironment.falseRaw (env : @& PyEnvironment) : Py.Raw :=
  .ofModel {env, addr := env.falseAddr, kind := .int, hint := .false}

open Internal in
public protected def Typing.false : Typing :=
  ofFn fun o => o.toModel.toInnerModel = o.toModel.env.falseRaw.toModel.toInnerModel

public instance : CoeDep Bool false Typing := ⟨.false⟩
public instance : ToTypeExpr false := ⟨false⟩

theorem PyEnvironment.falseRaw_hasType {env} : falseRaw env ⦂ false := by
  simp [PyEnvironment.falseRaw, Typing.false]

open PyEnvironment in
public instance : NonemptyPy false :=
  .intro (falseRaw Classical.ofNonempty) falseRaw_hasType

/-- A Python {lit}`False` constant. -/
public abbrev PyFalse := PyBoolView <| PyObjectView <| Py false

public instance : ViewPy false PyFalse := ⟨rfl⟩

open Classical in
@[extern "nerodia_py_object_is_false"]
def PyObject.isFalse (self : @& PyObject) : Bool :=
  self ⦂ false

open PyObject in
public instance : DecidablePy false := private_decl%
  (Internal.decPy isFalse fun _ => by simp [PyObject.isFalse])

/-- Returns a reference to the {lit}`False` constant. -/
@[extern "nerodia_py_environment_false"]
public def PyEnvironment.false (env : @& PyEnvironment) : PyFalse :=
  ⟨env.falseRaw, falseRaw_hasType⟩

/-- Returns the {lit}`False` constant of the Python environment. -/
@[extern "nerodia_get_py_false"]
public def getPyFalse : CPyBaseIO PyFalse :=
  PyBaseIO.toCPyBaseIO do (·.false) <$> getPyEnvironment

/-! ## bool -/

/--
The Python boolean type, [{lit}`bool`][1].

[1]: https://docs.python.org/3/library/functions.html#bool
-/
public opaque bool : Constant

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.bool : TypeExpr :=
  ⟨"bool"⟩

public instance : CoeDep Constant bool TypeExpr := ⟨.bool⟩

open Internal in
public protected def Typing.bool : Typing :=
  false ∪ true
  deriving NonemptyPy

public instance : CoeDep Constant bool Typing := ⟨.bool⟩
public instance : ToTypeExpr bool := ⟨bool⟩

@[grind _=_] public theorem bool_eq_false_union_true :
  Typing.bool = .false ∪ .true := by rfl

theorem false_subset_bool : Typing.false ⊆ bool := by
  simp [bool_eq_false_union_true, Typing.Subset.union_left]

public instance : IsSubtypeOf bool false := ⟨false_subset_bool⟩

theorem true_subset_bool : Typing.true ⊆ bool := by
  simp [bool_eq_false_union_true, Typing.Subset.union_right]

public instance : IsSubtypeOf bool true := ⟨true_subset_bool⟩

/-- A Python boolean object. That is, an instance of {lit}`bool`. -/
public abbrev PyBool := PyObjectView <| Py bool

public instance : ViewPy bool PyBool := ⟨rfl⟩

/-- Shorthand for {lean}`ToPy bool α` -/
public abbrev ToPyBool := ToPy bool

namespace PyBoolView

@[inline] public def toPyBool
  [ToPyBool α] (self : PyBoolView α)
: PyBool := toPy self

@[simp, grind =]
public theorem toPyObject_eq_toPy
  [ToPyBool α] (self : PyBoolView α)
: self.toPyBool = toPy (α := α) self := by rfl

public instance [ToPyBool α] :
  CoeOut (PyBoolView α) PyBool := ⟨toPyBool⟩

end PyBoolView

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
@[inline] public def PyBool.toBool (self : PyBool) : Bool :=
  self ⦂ true
