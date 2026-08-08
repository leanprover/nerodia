/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO
meta import Nerodia.Internal.ViewMethod

namespace Nerodia

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public def TypeExpr.none : TypeExpr :=
  ⟨"None"⟩

public instance : CoeDep (Option α) none TypeExpr := ⟨.none⟩

noncomputable opaque PyEnvironment.noneAddr (env : PyEnvironment) : Addr

open Internal in
noncomputable def PyEnvironment.noneRaw (env : @& PyEnvironment) : Py.Raw :=
  .ofModel {env, addr := env.noneAddr, hint := .none, kind := .other}

open Internal in
public def Typing.none : Typing :=
  ofFn fun o => o = o.toModel.env.noneRaw

public instance : CoeDep (Option α) none Typing := ⟨.none⟩
public instance : ToTypeExpr none := ⟨none⟩

theorem PyEnvironment.noneRaw_hasType {env} : noneRaw env ⦂ none := by
  simp [PyEnvironment.noneRaw, Typing.none]

open PyEnvironment in
public instance : NonemptyPy none :=
  .intro (noneRaw Classical.ofNonempty) noneRaw_hasType

/-- A Python {lit}`None` constant. -/
public abbrev PyNone := PyObjectView <| Py none

open Classical in
/-- Equivalent to the Python {lit}`self is None`. -/
@[extern "nerodia_py_object_is_none", view_method]
public def PyObject.isNone (self : @& PyObject) : Bool :=
  self ⦂ none

@[grind _=_]
public theorem PyObject.isNone_iff_hasType : isNone o ↔ o ⦂ none := by
  simp [PyObject.isNone]

open PyObject in
public instance : DecidablePy none := private_decl%
  (Internal.decPy isNone fun _ => isNone_iff_hasType)

@[simp] public theorem PyNone.isNone_eq_true : (o : PyNone).isNone = true := by
  simp [PyObject.isNone_iff_hasType]

/-- Returns a reference to the {lit}`None` constant. -/
@[extern "nerodia_py_environment_none"]
public def PyEnvironment.none (env : @& PyEnvironment) : PyNone :=
  ⟨env.noneRaw, noneRaw_hasType⟩

/-- Returns the {lit}`None` constant of the Python environment. -/
@[extern "nerodia_get_py_none"]
public def getPyNone : CPyBaseIO PyNone :=
  PyBaseIO.toCPyBaseIO do (·.none) <$> getPyEnvironment
