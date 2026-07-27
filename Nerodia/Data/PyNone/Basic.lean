/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO
meta import Nerodia.ViewMethod

namespace Nerodia

@[inline, irreducible, expose] public def TypeExpr.none : TypeExpr :=
  ⟨"None"⟩

public instance : CoeDep (Option α) none TypeExpr := ⟨.none⟩

noncomputable opaque PyEnvironment.noneAddr (env : PyEnvironment) : Addr

open Internal in
noncomputable def PyEnvironment.noneRaw (env : @& PyEnvironment) : Py.Raw :=
  .ofModel {env, addr := env.noneAddr, hint := .none, kind := .other}

open Internal in
public def TypePred.none : TypePred :=
  ofFn fun o => o = o.toModel.env.noneRaw

public instance : CoeDep (Option α) none TypePred := ⟨.none⟩
public instance : ToTypeExpr none := ⟨none⟩

theorem PyEnvironment.noneRaw_mem_none {env} : noneRaw env ∈ TypePred.none := by
  simp [PyEnvironment.noneRaw, TypePred.none]

open PyEnvironment in
public instance : NonemptyPy none :=
  .intro (noneRaw Classical.ofNonempty) noneRaw_mem_none

/--
The type of the Python {lit}`None` constant, [{lit}`types.NoneType`][1].

[1]: https://docs.python.org/3/library/types.html#types.NoneType
-/
@[inline, irreducible, expose] public def noneType : TypeConst :=
  ⟨"NoneType"⟩

/-- A Python {lit}`None` constant. -/
public abbrev PyNone := PyObjectView <| Py none

open Classical in
/-- Equivalent to the Python {lit}`self is None`. -/
@[extern "nerodia_py_object_is_none", view_method]
public def PyObject.isNone (self : PyObject) : Bool :=
  @decide (self.raw ∈ TypePred.none) (Classical.propDecidable _)

@[grind _=_]
public theorem PyObject.isNone_iff_mem : isNone o ↔ o.raw ∈ TypePred.none := by
  simp [PyObject.isNone]

public instance : DecidablePy none :=
  Internal.decPy (·.isNone) (·.isNone_iff_mem)

@[simp] public theorem PyNone.isNone_eq_true : (o : PyNone).isNone = true := by
  simp [PyObject.isNone_iff_mem]

/-- Returns a reference to the {lit}`None` constant. -/
@[extern "nerodia_py_environment_none"]
public def PyEnvironment.none (env : @& PyEnvironment) : PyNone :=
  ⟨env.noneRaw, noneRaw_mem_none⟩

/-- Returns the {lit}`None` constant of the Python environment. -/
@[extern "nerodia_get_py_none"]
public def getPyNone : CPyBaseIO PyNone :=
  PyBaseIO.toCPyBaseIO do (·.none) <$> getPyEnvironment
