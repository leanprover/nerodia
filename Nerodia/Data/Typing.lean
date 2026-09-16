/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.TypeExpr
public import Nerodia.Data.Py.Raw.Type

/-! # Typings -/

namespace Nerodia

/--
A typing predicate for Python objects.

This is the propositional equivalent of a Python type expression.
However, it can express more complex types (e.g., intersections) than Python's
base type system and is thus closer in power to the type system of Python's
more advanced type checkers (e.g., [{lit}`ty`][1]).

[1]: https://github.com/astral-sh/ty

**API Caveat:** The definition of {name}`Typing` is not part of Nerodia's
public API. Nevertheless, it is exposed due to the limitations of Lean's compiler.
-/
@[irreducible, expose] -- for codegen
public def Typing : Type :=
  Py.Raw → Prop

/--
Associates a Python type expression with a Nerodia type predicate.

This class is used by the Nerodia compiler to generate Python type annotations.
For this to work, all instances must be publicly reducible to {lean}`String`.
Thus, definitions they use must be marked {attr}`@[expose]`.
-/
public class ToTypeExpr (T : Typing) where
  toTypeExpr : TypeExpr

namespace Typing

export ToTypeExpr (toTypeExpr)

unseal Typing in
public def ofFn (p : Py.Raw → Prop) : Typing :=
  p

unseal Typing in
public def HasType (T : Typing) (o : Py.Raw) : Prop :=
  T o

end Typing

export Typing (HasType)

public section
scoped notation:50 o:51 " ⦂ " T:51 => Nerodia.HasType T o
end

recommended_spelling "hasType" for "⦂" in [«term_⦂_»]

/--
{given -show}`o : Py.Raw, T : Typing`
The typing relation {lean}`o ⦂ T : Prop` asserts that
the Python object {lean}`o` has the Python typing {lean}`T`.
-/
add_decl_doc «term_⦂_»

/-- Holds if {lean}`o` has the Python typing {lean}`T`. Written as {lean}`o ⦂ T`. -/
add_decl_doc HasType

namespace Typing

unseal Typing in
@[simp, grind =] public theorem hasType_ofFn_iff :
  o ⦂ ofFn p ↔ p o
:= Iff.intro id id

unseal Typing in
@[ext, grind ext] public theorem ext
  {T U : Typing} (h : ∀ o, o ⦂ T ↔ o ⦂ U) : T = U
:= funext fun o => propext (h o)

public protected def union (T : Typing) (U : Typing) : Typing :=
  ofFn fun o => o ⦂ T ∨ o ⦂ U

public instance : Union Typing := ⟨Typing.union⟩

/--
Constructs the union of two typings.
Written as {lean}`T ∪ U`. Equivalent to the Python `T | U`.
-/
add_decl_doc Typing.union

@[grind =] public theorem hasType_union_iff_or {T U : Typing} :
  o ⦂ T ∪ U ↔ o ⦂ T ∨ o ⦂ U
:= by simp only [Union.union, Typing.union, hasType_ofFn_iff]

public theorem HasType.union_left
  {T U : Typing} (h : o ⦂ T) : o ⦂ T ∪ U
:= hasType_union_iff_or.mpr <| .inl h

public theorem HasType.union_right
  {T U : Typing} (h : o ⦂ U) : o ⦂ T ∪ U
:= hasType_union_iff_or.mpr <| .inr h

public protected def inter (T : Typing) (U : Typing) : Typing :=
  ofFn fun o => o ⦂ T ∧ o ⦂ U

public instance : Inter Typing := ⟨Typing.inter⟩

/--
Constructs the intersection of two type predicates. Written as {lean}`T ∩ U`.

Python's type system has no equivalent, but [ty][1] represents this
as {lit}`T & U` / {lit}`Intersection[T, U]`.

[1]: https://docs.astral.sh/ty/features/type-system/#intersection-types
-/
add_decl_doc Typing.inter

@[grind =] public theorem hasType_inter_iff_and {T U : Typing} :
  o ⦂ T ∩ U ↔ o ⦂ T ∧ o ⦂ U
:= by simp only [Inter.inter, Typing.inter, hasType_ofFn_iff]

public nonrec theorem HasType.left
  {T U : Typing} (h : o ⦂ T ∩ U) : o ⦂ T
:= hasType_inter_iff_and.mp h |>.left

public nonrec theorem HasType.right
  {T U : Typing} (h : o ⦂ T ∩ U) : o ⦂ U
:= hasType_inter_iff_and.mp h |>.right

public def Subset (T : Typing) (U : Typing) : Prop :=
  ∀ o, o ⦂ T → o ⦂ U

public instance : HasSubset Typing := ⟨Subset⟩

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

public theorem Subset.inter_left {T U : Typing} : T ∩ U ⊆ T :=
  subset_iff_forall.mpr fun _ => .left

public theorem Subset.inter_right {T U : Typing} : T ∩ U ⊆ U :=
  subset_iff_forall.mpr fun _ => .right

public theorem Subset.union_left {T U : Typing} : T ⊆ T ∪ U :=
  subset_iff_forall.mpr fun _ => .union_left

public theorem Subset.union_right {T U : Typing} : T ⊆ U ∪ T :=
  subset_iff_forall.mpr fun _ => .union_right

/-- Python {lit}`object`. The top (⊤) element of the set of typings. -/
public def object : Typing :=
  ofFn fun _ => True

@[simp, grind .] public theorem HasType.object : o ⦂ object := by
  simp only [Typing.object, hasType_ofFn_iff]

-- the below are `@[simp]` only because grind already handles them

@[simp] public theorem Subset.object : T ⊆ object :=
  subset_iff_forall.mpr fun _ _ => .object

@[simp] public theorem union_object : T ∪ object = object := by
  simp [Typing.ext_iff, hasType_union_iff_or]

@[simp] public theorem object_union : object ∪ T = object := by
  simp [Typing.ext_iff, hasType_union_iff_or]

@[simp] public theorem inter_object : T ∩ object = T := by
  simp [Typing.ext_iff, hasType_inter_iff_and]

@[simp] public theorem object_inter : object ∩ T = T := by
  simp [Typing.ext_iff, hasType_inter_iff_and]

/-- Python {lit}`Never`. The bottom (⊥) element of the set of typings. -/
public def never : Typing :=
  ofFn fun _ => False

@[simp, grind .] public theorem not_hasType_never : ¬ o ⦂ never := by
  simp [never]

-- the below are `@[simp]` only because grind already handles them

@[simp] public theorem Subset.never : never ⊆ T :=
  subset_iff_forall.mpr fun _ => not_hasType_never.elim

@[deprecated Subset.never (since := "2026-09-11")]
public theorem never_subset : never ⊆ T := Subset.never

@[simp] public theorem union_never : T ∪ never = T := by
  simp [Typing.ext_iff, hasType_union_iff_or]

@[simp] public theorem never_union : never ∪ T = T := by
  simp [Typing.ext_iff, hasType_union_iff_or]

@[simp] public theorem inter_never : T ∩ never = never := by
  simp [Typing.ext_iff, hasType_inter_iff_and]

@[simp] public theorem never_inter : never ∩ T = never := by
  simp [Typing.ext_iff, hasType_inter_iff_and]

end Typing

public instance [ToTypeExpr T] [ToTypeExpr U] : ToTypeExpr (T ∪ U) where
  toTypeExpr:= .union (ToTypeExpr.toTypeExpr T) (ToTypeExpr.toTypeExpr U)

/-! ## Type Promotion -/

/--
Bidirectional type promotion from {lean}`U` to {lean}`T`.

Promotes a concrete subtype to a concrete supertype
(e.g., {lit}`bool` to {lit}`int`).
-/
public class PromotableB (T U : semiOutParam Typing) : Prop where
  intro :: infer : U ⊆ T

/--
Type promotion from {lean}`U` to {lean}`T` chained right-to-left (i.e., downwards).

Promotes a subtype to a concrete supertype (e.g., {lit}`T ∩ U` to {lit}`T`).
-/
public class PromotableRtl (T : semiOutParam Typing) (U : Typing) : Prop where
  intro :: infer : U ⊆ T

/--
Type promotion from {lean}`U` to {lean}`T` chained left-to-right (i.e., upwards).

Promotes a concrete subtype to a supertype (e.g., {lit}`T` to {lit}`T ∪ U`)..
-/
public class PromotableLtr (T : Typing) (U : semiOutParam Typing) : Prop where
  intro :: infer : U ⊆ T

/--
Transitive chain of type promotions from {lean}`U` to {lean}`T`.

Has the form: `PromotableOut* PromotableIn*`.
-/
public class PromotableT (T : Typing) (U : Typing) : Prop where
  intro :: infer : U ⊆ T

public instance [PromotableB T U] : PromotableRtl T U := ⟨PromotableB.infer⟩
public instance [PromotableB T U] : PromotableLtr T U := ⟨PromotableB.infer⟩

public instance [PromotableT T U] [PromotableRtl U V] : PromotableT T V :=
  ⟨@Typing.Subset.trans V U T PromotableRtl.infer PromotableT.infer⟩

public instance [PromotableLtr T U] [PromotableT U V] : PromotableT T V :=
  ⟨@Typing.Subset.trans V U T PromotableT.infer PromotableLtr.infer⟩

@[default_instance] public instance : PromotableT T T := ⟨.rfl⟩

/-- Type promotion from {lean}`U` to {lean}`T`. -/
public class Promotable (T : Typing) (U : Typing) : Prop where
  intro :: infer : U ⊆ T

public instance [PromotableT T U]  : Promotable T U := ⟨PromotableT.infer⟩
@[default_instance] public instance : Promotable T T := ⟨.rfl⟩

public theorem subset_of_promotable [Promotable T U] : U ⊆ T :=
  Promotable.infer

public instance : Promotable T .never := ⟨.never⟩
public instance : Promotable .object T := ⟨.object⟩
public instance : PromotableRtl T (T ∩ U) := ⟨.inter_left⟩
public instance : PromotableRtl U (T ∩ U) := ⟨.inter_right⟩
public instance : PromotableLtr (T ∪ U) T := ⟨.union_left⟩
public instance : PromotableLtr (T ∪ U) U := ⟨.union_right⟩

/-- Type class used to automatically infer supertypes. -/
public class IsSubtypeOf (T U : Typing) : Prop where
  infer_subtype : U ⊆ T

export IsSubtypeOf (infer_subtype)

public instance [Promotable T U] : IsSubtypeOf T U := ⟨Promotable.infer⟩
public instance [IsSubtypeOf T U] : Promotable T U := ⟨infer_subtype⟩

attribute [deprecated "Use one of the `Promotable` classes." (since := "2026-09-16")] IsSubtypeOf
attribute [deprecated subset_of_promotable (since := "2026-09-16")] infer_subtype
