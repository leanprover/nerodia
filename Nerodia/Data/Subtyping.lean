/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Typing.Promotable

/-! # Subtyping -/

namespace Nerodia

/--
A typing predicate for instances of {lean}`T`.

{lean}`Subtyping` provides a convientent way to define typing predicates
which  depend on API of the a more narrow type than {lit}`object`. For example,
a subtyping of {lit}`tuple` can be defined over its array representation.
-/
@[irreducible, expose]
public def Subtyping (T : Typing) :=
  (x : PyObject) → x ⦂ T → Prop

unseal Subtyping in
/-- A subtype of {lean}`T`. Allows the predicate {lean}`S` to depend on {lean}`T`. -/
@[irreducible] public def Typing.subtype (T : Typing) (S : Subtyping T) : Typing :=
  .ofFn fun x => ∃ h : x ⦂ T, S x h

public instance : CoeHead (Subtyping T) Typing := ⟨.subtype T⟩

unseal Subtyping in
@[simp, grind .] public theorem Typing.subtype_subset : subtype T U ⊆ T := by
  grind [Typing.subtype]

public instance : PromotableRtl T (.subtype T U) := ⟨Typing.subtype_subset⟩

/-! ## Basics -/

namespace Subtyping

unseal Subtyping in
public def ofFn (p : (x : PyObject) → x ⦂ T → Prop) : Subtyping T :=
  p

unseal Subtyping Typing.subtype in
public theorem ofFn_iff :
  x ⦂ @ofFn T p ↔ ∃ h, p x h
:= by simp [Typing.subtype, Typing.ofFn_iff, Subtyping.ofFn]

-- `congr_simp` helper is ill-typed w/ `unseal Subtyping` and panics
attribute [grind =] ofFn_iff

unseal Subtyping in
@[ext, grind ext] public theorem ext
  {U V : Subtyping T} (h : T.subtype U = T.subtype V)
: U = V := by
  funext x
  ext
  simp only [Typing.subtype, Typing.ext_iff, Typing.ofFn_iff] at h
  grind

end Subtyping

/-! ## {lit}`any` -/

/-- A subtyping predicate accetping any instance of {lean}`T`. -/
public protected def Subtyping.any : Subtyping T :=
  .ofFn fun _ _ => True

@[simp, grind =] public theorem Typing.subtype_any : subtype T .any = T := by
  simp [Typing.ext_iff, Subtyping.any, Subtyping.ofFn_iff]

public instance [NonemptyPy T] : NonemptyPy (.subtype T .any) :=
  have x : Py T := Classical.ofNonempty
  have : Promotable (.subtype T .any) T := ⟨by rw [Typing.subtype_any]⟩
  ⟨x.promote⟩

public instance [DecidablePy T] : DecidablePy (.subtype T .any) := private_decl%
  fun x =>  decidable_of_decidable_of_eq (p := x ⦂ T) (by rw [Typing.subtype_any])
