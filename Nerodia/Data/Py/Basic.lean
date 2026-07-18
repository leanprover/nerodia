/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.TypePred
public import Nerodia.Data.Py.Raw.Type

/-! # Py -/

namespace Nerodia

/-- A typed Python object. -/
public structure Py (T : TypePred) where
  raw : Py.Raw
  raw_mem : raw ∈ T

namespace Py

attribute [simp, grind! .] Py.raw_mem

@[inline] public def left (self : Py (T ∩ U)) : Py T :=
  mk self.raw self.raw_mem.left

@[simp, grind =] public theorem raw_left : (left o).raw = o.raw := by rfl

@[inline] public def right (self : Py (T ∩ U)) : Py U :=
  mk self.raw self.raw_mem.right

@[simp, grind =] public theorem raw_right : (right o).raw = o.raw := by rfl

end Py

/-! ## IsPy -/

public class inductive IsPy : (α : Type) → Prop
| of_raw : IsPy Py.Raw
| of_py {T} : IsPy (Py T)

namespace IsPy
public instance : IsPy Py.Raw := .of_raw
public instance : IsPy (Py T) := .of_py
end IsPy

/-! ## NonemptyPy -/

public abbrev NonemptyPy (T : TypePred) := Nonempty (Py T)

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

public class ToPy (T : TypePred) (α : Type u)  where
  toPy (a : α) : Py T

export ToPy (toPy)

namespace ToPy

public instance : ToPy T (Py T) := ⟨(·)⟩

@[simp, grind =] public theorem toPy_eq_self :
  toPy (o : Py T) = o := by rfl

public instance : ToPy T (Py (T ∩ U)) := ⟨Py.left⟩

@[simp, grind =] public theorem toPy_eq_left  :
  toPy (o : Py  (T ∩ U)) = o.left := by rfl

public instance : ToPy U (Py (T ∩ U)) := ⟨Py.right⟩

@[simp, grind =] public theorem toPy_eq_right :
  toPy (o : Py (T ∩ U)) = o.right := by rfl

public instance [ToPy T Py.Raw] : ToPy T (Py U) := ⟨(toPy ·.raw)⟩

@[simp, grind =] public theorem toPy_eq_toPy_raw  [ToPy U Py.Raw] :
  toPy (o : Py T) = toPy (T := U) o.raw := by rfl

end ToPy
