/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Py.Raw
public import Nerodia.Data.TypeExpr

/-! # Type Predicate -/

namespace Nerodia

/-- A Neordia type predicate. -/
@[expose] -- for Lean/Nerodia codegen
public def TypePred : Type :=
  Py.Raw → Prop

/--
Associates a Python type expression with a Nerodia type predicate.

This class is used by the Nerodia compiler to generate Python type annotations.
For this to work, all instances must be publicly reducible to {lean}`String`.
Thus, definitions they use must be marked {attr}`@[expose]`.
-/
public class ToTypeExpr (T : TypePred) where
  toTypeExpr : TypeExpr

namespace TypePred

public def ofFn (p : Py.Raw → Prop) : TypePred :=
  p

public def Mem (T : TypePred) (o : Py.Raw) : Prop :=
  T o

public instance : Membership Py.Raw TypePred := ⟨Mem⟩

@[simp, grind =] public theorem mem_ofFn :
  o ∈ ofFn p ↔ p o
:= Iff.intro id id

@[ext, grind ext] public theorem ext
  {T U : TypePred} (h : ∀ o, o ∈ T ↔ o ∈ U) : T = U
:= funext fun o => propext (h o)

public def union (T : TypePred) (U : TypePred) : TypePred :=
  ofFn fun o => o ∈ T ∨ o ∈ U

public instance : Union TypePred := ⟨union⟩

/--
Constructs the union of two type predicates.
Written as {lean}`T ∪ U`. Equivalent to the Python `T | U`.
-/
add_decl_doc union

@[grind =] public theorem mem_union_iff_or {T U : TypePred} :
  o ∈ T ∪ U ↔ o ∈ T ∨ o ∈ U
:= Iff.intro id id

public theorem Mem.union_left
  {T U : TypePred} (h : o ∈ T) : o ∈ T ∪ U
:= .inl h

public theorem Mem.union_right
  {T U : TypePred} (h : o ∈ U) : o ∈ T ∪ U
:= .inr h

/-- Constructs the union of two type predicates. Equivalent to the Python `T | U`. -/
public def inter (T : TypePred) (U : TypePred) : TypePred :=
  ofFn fun o => o ∈ T ∧ o ∈ U

public instance : Inter TypePred := ⟨inter⟩

/--
Constructs the intersection of two type predicates. Written as {lean}`T ∩ U`.

Python's type system has no equivalent, but [ty][1] represents this
as {lit}`T & U` / {lit}`Intersection[T, U]`.

[1]: https://docs.astral.sh/ty/features/type-system/#intersection-types
-/
add_decl_doc inter

@[grind =] public theorem mem_inter_iff_and {T U : TypePred} :
  o ∈ T ∩ U ↔ o ∈ T ∧ o ∈ U
:= Iff.intro id id

public nonrec theorem Mem.left
  {T U : TypePred} (h : o ∈ T ∩ U) : o ∈ T
:= h.left

public nonrec theorem Mem.right
  {T U : TypePred} (h : o ∈ T ∩ U) : o ∈ U
:= h.right

public def Subset (T : TypePred) (U : TypePred) : Prop :=
  ∀ o, o ∈ T → o ∈ U

public instance : HasSubset TypePred := ⟨Subset⟩

@[grind =] public theorem subset_iff_forall {T U : TypePred} :
  T ⊆ U ↔ ∀ o, o ∈ T → o ∈ U
:= Iff.intro id id

public theorem Subset.mem_of_mem
  {T U : TypePred} (h : T ⊆ U) (ho : o ∈ T)
: o ∈ U := subset_iff_forall.mp h o ho

/-- Python {lit}`object`. The top (⊤) element of type predicates. -/
public def object : TypePred :=
  ofFn fun _ => True

@[simp, grind .] public theorem Mem.object : o ∈ object := True.intro

-- the below are `@[simp]` only because grind already handles them

@[simp] public theorem Subset.object : T ⊆ object :=
  subset_iff_forall.mpr fun _ _ => .object

@[simp] public theorem union_object : T ∪ object = object := by
  simp [TypePred.ext_iff, mem_union_iff_or]

@[simp] public theorem object_union : object ∪ T = object := by
  simp [TypePred.ext_iff, mem_union_iff_or]

@[simp] public theorem inter_object : T ∩ object = T := by
  simp [TypePred.ext_iff, mem_inter_iff_and]

@[simp] public theorem object_inter : object ∩ T = T := by
  simp [TypePred.ext_iff, mem_inter_iff_and]

/-- Python {lit}`Never`. The bottom (⊥) element of type predicates. -/
public def never : TypePred :=
  ofFn fun _ => False

@[simp, grind .] public theorem not_mem_never : ¬ o ∈ never := by
  simp [never]

-- the below are `@[simp]` only because grind already handles them

@[simp] public theorem never_subset : never ⊆ T :=
  subset_iff_forall.mpr fun _ => not_mem_never.elim

@[simp] public theorem union_never : T ∪ never = T := by
  simp [TypePred.ext_iff, mem_union_iff_or]

@[simp] public theorem never_union : never ∪ T = T := by
  simp [TypePred.ext_iff, mem_union_iff_or]

@[simp] public theorem inter_never : T ∩ never = never := by
  simp [TypePred.ext_iff, mem_inter_iff_and]

@[simp] public theorem never_inter : never ∩ T = never := by
  simp [TypePred.ext_iff, mem_inter_iff_and]
