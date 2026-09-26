/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Typing.Ops

/-! # Type Promotion -/

namespace Nerodia

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

Has the form: `PromotableLtr* PromotableRtl*`.
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

public theorem Typing.Subset.of_promotable [Promotable T U] : U ⊆ T :=
  Promotable.infer

public instance : Promotable T .never := ⟨.never⟩
public instance : Promotable .object T := ⟨.object⟩
public instance : PromotableRtl T (T ∩ U) := ⟨.inter_left⟩
public instance : PromotableRtl U (T ∩ U) := ⟨.inter_right⟩
public instance : PromotableLtr (T ∪ U) T := ⟨.union_left⟩
public instance : PromotableLtr (T ∪ U) U := ⟨.union_right⟩

/-! ## Promoting Objects -/

public theorem PyObject.HasType.promote
  [Promotable T U] (h : self ⦂ U) : self ⦂ T
:= Typing.Subset.of_promotable.hasType_of_hasType h

/--
**Type promotion.**
Casts a Python object from {lean}`U` to its supertype {lean}`T`.
-/
@[inline] public def Py.promote [Promotable T U] (self : Py U) : Py T :=
  ofPyObject self self.toPyObject_hasType.promote

public instance [Promotable T U] : ToPy T (Py U) := ⟨Py.promote⟩

@[simp, grind =] public theorem toPy_eq_promote [Promotable T U] :
  toPy o = Py.promote o (T := T) (U := U) := by rfl

/-! ## IsSubtypeOf -/

/-- Type class used to automatically infer supertypes. -/
public class IsSubtypeOf (T U : Typing) : Prop where
  infer_subtype : U ⊆ T

export IsSubtypeOf (infer_subtype)

public instance [Promotable T U] : IsSubtypeOf T U := ⟨Promotable.infer⟩
public instance [IsSubtypeOf T U] : Promotable T U := ⟨infer_subtype⟩

attribute [deprecated "Use one of the `Promotable` classes." (since := "2026-09-16")] IsSubtypeOf
attribute [deprecated Typing.Subset.of_promotable +typeChanged (since := "2026-09-16")] infer_subtype
