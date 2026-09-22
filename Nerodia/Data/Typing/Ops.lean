/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.PyNever

/-! # Typing Operations -/

namespace Nerodia.Typing

/-! ## Union -/

public protected def union (T : Typing) (U : Typing) : Typing :=
  ofFn fun o => o ⦂ T ∨ o ⦂ U

public instance : Union Typing := ⟨Typing.union⟩

@[grind =] public theorem union_iff_or {T U : Typing} :
  o ⦂ T ∪ U ↔ o ⦂ T ∨ o ⦂ U
:= by simp only [Union.union, Typing.union, ofFn_iff]

@[deprecated union_iff_or (since := "2026-09-20")]
public theorem hasType_union_iff_or {T U : Typing} :
  o ⦂ T ∪ U ↔ o ⦂ T ∨ o ⦂ U := union_iff_or

/--
Constructs the union of two typings.
Written as {lean}`T ∪ U`. Equivalent to the Python `T | U`.
-/
add_decl_doc Typing.union

public instance [ToTypeExpr T] [ToTypeExpr U] : ToTypeExpr (T ∪ U) where
  toTypeExpr:= .union (ToTypeExpr.toTypeExpr T) (ToTypeExpr.toTypeExpr U)

public instance [DecidablePy T] [DecidablePy U] : DecidablePy (T ∪ U) := private_decl%
  fun _ => decidable_of_iff' _ Typing.union_iff_or

/-! ## Intersection -/

public protected def inter (T : Typing) (U : Typing) : Typing :=
  ofFn fun o => o ⦂ T ∧ o ⦂ U

public instance : Inter Typing := ⟨Typing.inter⟩

@[grind =] public theorem inter_iff_and {T U : Typing} :
  o ⦂ T ∩ U ↔ o ⦂ T ∧ o ⦂ U
:= by simp only [Inter.inter, Typing.inter, ofFn_iff]

@[deprecated inter_iff_and (since := "2026-09-20")]
public theorem hasType_inter_iff_and {T U : Typing} :
  o ⦂ T ∩ U ↔ o ⦂ T ∧ o ⦂ U := inter_iff_and

/--
Constructs the intersection of two type predicates. Written as {lean}`T ∩ U`.

Python's type system has no equivalent, but [ty][1] represents this
as {lit}`T & U` / {lit}`Intersection[T, U]`.

[1]: https://docs.astral.sh/ty/features/type-system/#intersection-types
-/
add_decl_doc Typing.inter

public instance [DecidablePy T] [DecidablePy U] : DecidablePy (T ∩ U) := private_decl%
  fun _ => decidable_of_iff' _ Typing.inter_iff_and

/-! ## Subset (Subtype) -/

public def Subset (T : Typing) (U : Typing) : Prop :=
  ∀ o, o ⦂ T → o ⦂ U

public instance : HasSubset Typing := ⟨Subset⟩

/--
{given -show}`T : Typing, U : Typing`
{lean}`Subset T U` holds if {lean}`T` is a subtype of {lean}`U`.
Written as {lean}`T ⊆ U`.
-/
add_decl_doc Subset

@[grind =] public theorem subset_iff_forall {T U : Typing} :
  T ⊆ U ↔ ∀ o, o ⦂ T → o ⦂ U
:= Iff.intro id id

public theorem Subset.hasType_of_hasType
  {T U : Typing} (h : T ⊆ U) (ho : o ⦂ T)
: o ⦂ U := subset_iff_forall.mp h o ho

@[refl] public theorem Subset.refl (T : Typing) : T ⊆ T :=
  subset_iff_forall.mpr fun _ => id

public theorem Subset.rfl {T : Typing} : T ⊆ T :=
  .refl T

public theorem Subset.trans {T U V : Typing} (h₁ : T ⊆ U) (h₂ : U ⊆ V) : T ⊆ V :=
  subset_iff_forall.mpr fun _ h => h₂.hasType_of_hasType (h₁.hasType_of_hasType h)

end Typing

public theorem PyObject.HasType.left
  {T U : Typing} (h : o ⦂ T ∩ U) : o ⦂ T
:= Typing.inter_iff_and.mp h |>.left

public theorem PyObject.HasType.right
  {T U : Typing} (h : o ⦂ T ∩ U) : o ⦂ U
:= Typing.inter_iff_and.mp h |>.right

public theorem PyObject.HasType.union_left
  {T U : Typing} (h : o ⦂ T) : o ⦂ T ∪ U
:= Typing.union_iff_or.mpr <| .inl h

public instance [NonemptyPy T] : NonemptyPy (T ∪ U) :=
  let o : Py T := Classical.ofNonempty
  ⟨.ofPyObject o o.toPyObject_hasType.union_left⟩

public theorem PyObject.HasType.union_right
  {T U : Typing} (h : o ⦂ U) : o ⦂ T ∪ U
:= Typing.union_iff_or.mpr <| .inr h

public instance [NonemptyPy U] : NonemptyPy (T ∪ U) :=
  let o : Py U := Classical.ofNonempty
  ⟨.ofPyObject o o.toPyObject_hasType.union_right⟩

@[deprecated PyObject.HasType.left (since := "2026-09-22")]
public abbrev Typing.HasType.left := @PyObject.HasType.left

@[deprecated PyObject.HasType.right (since := "2026-09-22")]
public abbrev Typing.HasType.right := @PyObject.HasType.right

/-! ## Inter-Operation Relations -/

namespace Typing

public theorem Subset.inter_left {T U : Typing} : T ∩ U ⊆ T :=
  subset_iff_forall.mpr fun _ => .left

public theorem Subset.inter_right {T U : Typing} : T ∩ U ⊆ U :=
  subset_iff_forall.mpr fun _ => .right

public theorem Subset.union_left {T U : Typing} : T ⊆ T ∪ U :=
  subset_iff_forall.mpr fun _ => .union_left

public theorem Subset.union_right {T U : Typing} : T ⊆ U ∪ T :=
  subset_iff_forall.mpr fun _ => .union_right

-- the below are `@[simp]` only because grind already handles them

@[simp] public theorem Subset.object : T ⊆ object :=
  subset_iff_forall.mpr fun _ _ => .object

@[simp] public theorem union_object : T ∪ object = object := by
  simp [Typing.ext_iff, union_iff_or]

@[simp] public theorem object_union : object ∪ T = object := by
  simp [Typing.ext_iff, union_iff_or]

@[simp] public theorem inter_object : T ∩ object = T := by
  simp [Typing.ext_iff, inter_iff_and]

@[simp] public theorem object_inter : object ∩ T = T := by
  simp [Typing.ext_iff, inter_iff_and]

-- the below are `@[simp]` only because grind already handles them

@[simp] public theorem Subset.never : never ⊆ T :=
  subset_iff_forall.mpr fun _ h => h.not_never.elim

@[deprecated Subset.never (since := "2026-09-11")]
public theorem never_subset : never ⊆ T := Subset.never

@[simp] public theorem union_never : T ∪ never = T := by
  simp [Typing.ext_iff, union_iff_or]

@[simp] public theorem never_union : never ∪ T = T := by
  simp [Typing.ext_iff, union_iff_or]

@[simp] public theorem inter_never : T ∩ never = never := by
  simp [Typing.ext_iff, inter_iff_and]

@[simp] public theorem never_inter : never ∩ T = never := by
  simp [Typing.ext_iff, inter_iff_and]

end Typing
