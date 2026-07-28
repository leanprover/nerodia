/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Typing
public import Nerodia.Data.Py.Raw.Type

/-! # Py -/

namespace Nerodia

/-- A typed Python object. -/
public structure Py (T : Typing) where
  raw : Py.Raw
  raw_mem : raw ∈ T

namespace Py

attribute [simp, grind! .] Py.raw_mem

/--
**Type promotion.**
Casts a Python object from {lean}`U` to its supertype {lean}`T`.
-/
@[inline] public def promote (self : Py U) [IsSubtypeOf T U] : Py T :=
  mk self.raw <| infer_subtype.mem_of_mem self.raw_mem

@[simp, grind =] public theorem raw_promote [IsSubtypeOf T U] :
  (promote (T := T) (U := U) o).raw = o.raw := by rfl

end Py

/-! ## IsPy -/

/--
{lean}`IsPy α` holds if {lean}`α` is a type
represented at runtime by a managed Python object pointer.
-/
public class inductive IsPy : (α : Type) → Prop
| private of_raw : IsPy Py.Raw
| private of_py {T} : IsPy (Py T)

public instance : IsPy Py.Raw := .of_raw
public instance : IsPy (Py T) := .of_py

/-! ## DecidablePy -/

/--
A typing {lean}`T` with a {lean}`DecidablePy T` instance
has a pure type checking function.
-/
public abbrev DecidablePy (T : Typing) := DecidablePred (· ∈ T)

public instance [DecidablePy T] [DecidablePy U] : DecidablePy (T ∪ U) :=
  fun _ => decidable_of_iff' _ Typing.mem_union_iff_or

public instance [DecidablePy T] [DecidablePy U] : DecidablePy (T ∩ U) :=
  fun _ => decidable_of_iff' _ Typing.mem_inter_iff_and

/-! ## NonemptyPy -/

/--
A {lean}`NonemptyPy T` instance provides a proof
that there exists a Python object of type {lean}`T`.
-/
public abbrev NonemptyPy (T : Typing) := Nonempty (Py T)

public theorem NonemptyPy.intro (o : Py.Raw) (h : o ∈ T) : NonemptyPy T :=
  ⟨⟨o, h⟩⟩

public instance : NonemptyPy .object :=
  .intro Classical.ofNonempty .object

public instance [NonemptyPy T] : NonemptyPy (T ∪ U) :=
  let o : Py T := Classical.ofNonempty
  .intro o.raw o.raw_mem.union_left

public instance [NonemptyPy U] : NonemptyPy (T ∪ U) :=
  let o : Py U := Classical.ofNonempty
  .intro o.raw o.raw_mem.union_right

/-! ## ToPy -/

/--
Types which can be trivially converted into Python objects of type {lean}`T`.

This type class is intended to be used to convert between different
representations of a Python object (e.g., coverting a {lean}`Py T` to a
{given -show}`U : Typing` {lean}`Py (T ∩ U)`). It is not meant to be a
general way to construct Python objects from arbitrary Lean types.
-/
public class ToPy (T : Typing) (α : Type u)  where
  toPy (a : α) : Py T

export ToPy (toPy)

public instance [IsSubtypeOf T U] : ToPy T (Py U) := ⟨(·.promote)⟩

@[simp, grind =] public theorem toPy_eq_promote [IsSubtypeOf T U] :
  toPy o = Py.promote o (T := T) (U := U) := by rfl

public instance : ToPy T (Py T) := ⟨(·)⟩

@[simp, grind =] public theorem toPy_eq_self :
  toPy (o : Py T) = o := by rfl

public instance [ToPy T Py.Raw] : ToPy T (Py U) := ⟨(toPy ·.raw)⟩

@[simp, grind =] public theorem toPy_eq_toPy_raw  [ToPy U Py.Raw] :
  toPy (o : Py T) = toPy (T := U) o.raw := by rfl
