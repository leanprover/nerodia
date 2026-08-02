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
  raw_hasType : raw ⦂ T

namespace Py

public instance : CoeOut (Py T) Py.Raw := ⟨raw⟩

attribute [simp, grind! .] Py.raw_hasType

/--
**Type promotion.**
Casts a Python object from {lean}`U` to its supertype {lean}`T`.
-/
@[inline] public def promote (self : Py U) [IsSubtypeOf T U] : Py T :=
  mk self.raw <| infer_subtype.hasType_of_hasType self.raw_hasType

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
public abbrev DecidablePy (T : Typing) := DecidablePred (· ⦂ T)

public instance [DecidablePy T] [DecidablePy U] : DecidablePy (T ∪ U) :=
  fun _ => decidable_of_iff' _ Typing.hasType_union_iff_or

public instance [DecidablePy T] [DecidablePy U] : DecidablePy (T ∩ U) :=
  fun _ => decidable_of_iff' _ Typing.hasType_inter_iff_and

/-! ## NonemptyPy -/

/--
A {lean}`NonemptyPy T` instance provides a proof
that there exists a Python object of type {lean}`T`.
-/
public abbrev NonemptyPy (T : Typing) := Nonempty (Py T)

public theorem NonemptyPy.intro (o : Py.Raw) (h : o ⦂ T) : NonemptyPy T :=
  ⟨⟨o, h⟩⟩

public instance : NonemptyPy .object :=
  .intro Classical.ofNonempty .object

public instance [NonemptyPy T] : NonemptyPy (T ∪ U) :=
  let o : Py T := Classical.ofNonempty
  .intro o.raw o.raw_hasType.union_left

public instance [NonemptyPy U] : NonemptyPy (T ∪ U) :=
  let o : Py U := Classical.ofNonempty
  .intro o.raw o.raw_hasType.union_right

/-! ## ViewPy -/

/--
The instance {lean}`ViewPy T α` defines {lean}`α` as
the Lean view type corresponding to the Python typing {lean}`T`.

While {lean}`Py T` is the uniform Lean data type that attaches a typing to a
Python object, it is not equipped with the dot notation methods specific to said
type. Instead, the dot notation is defined on definitionally equal view types
(e.g., {name (scope := "Nerodia.Data.Types")}`PyStr`). {lean}`ViewPy` serves to
bridge the two, synthesizing the view type {lean}`α` from its respective typing
{lean}`T`.
-/
public class ViewPy (T : Typing) (α : outParam $ Type) : Prop where
  isPyT : α = Py T

public instance (priority := low) : ViewPy T (Py T) := ⟨rfl⟩

@[inline] def Py.Raw.attachType
  [ViewPy T α] (self : Py.Raw) (h : self ⦂ T)
: α := cast ViewPy.isPyT.symm (Py.mk self h)

@[simp] theorem Py.Raw.raw_attachType : (attachType o h).raw = o := by
  simp [attachType]

/--
Types {lean}`self` as {lean}`T` using a proof of correctness.

For example, the following pattern in Python:

```
if isinstance(self, T):
  # Python type checkers would assume `self: T` in this block
  fnT(self)
else:
  notT
```

can be implemented in Lean like so:

{givenInstance -show}`DecidablePy T`
{given -show}`fnT : α → Unit, notT : Unit`
```leanTerm
if h : self ⦂ T then
  let self := self.attachType h
  fnT self
else
  notT
```
-/
@[inline] public def Py.attachType
  [ViewPy T α] (self : Py U) (h : self ⦂ T)
: α := self.raw.attachType h

@[simp, grind =] public theorem Py.raw_attachType :
  ((o : Py T).attachType h).raw = o.raw
:= by simp [attachType]

/-! ## ToPy -/

/--
Types which can be trivially converted into Python objects of type {lean}`T`.

This type class is intended to be used to convert between different
representations of a Python object (e.g., converting a {lean}`Py T` to a
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
