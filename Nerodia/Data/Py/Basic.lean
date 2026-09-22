/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Typing.Raw
public import Nerodia.Data.Py.Raw.Type

/-! # Py -/

namespace Nerodia

public protected structure Internal.Py (T : Typing) where
  private mk ::
    private raw : Py.Raw
    private raw_hasType : raw.HasType T

/-- A typed Python object. -/
@[irreducible, expose] -- for codegen
public def Py (T : Typing) := Internal.Py T

/-! ## IsPy -/

/--
{lean}`IsPy α` holds if {lean}`α` is a type
represented at runtime by a managed Python object pointer.
-/
public class inductive IsPy : (α : Type) → Prop
| private of_py {T} : IsPy (Py T)
| private of_raw : IsPy Internal.Py.Raw

public instance : IsPy (Py T) := .of_py
namespace Internal
public instance : IsPy Internal.Py.Raw := .of_raw
end Internal

/-! ## ToPy -/

/--
Types which can be trivially converted into Python objects of type {lean}`T`.

This type class is intended to be used to convert between different
representations of a Python object (e.g., converting a {lean}`Py T` to a
{lean}`Py object`). It is not meant to be a general way to construct Python
objects from arbitrary Lean types.
-/
public class ToPy (T : Typing) (α : Type u)  where
  toPy (a : α) : Py T

export ToPy (toPy)

@[default_instance]
public instance : ToPy T (Py T) := ⟨(·)⟩

@[simp, grind =] public theorem toPy_eq_self :
  toPy (o : Py T) = o := by rfl


/-! ## PyObject -/

/-- Any Python object. That is, an instance of {lit}`object`. -/
public abbrev PyObject := Py object

/-- Shorthand for {lean}`ToPy object α` -/
public abbrev ToPyObject := ToPy object

namespace Py

unseal Py in
@[inline] public def toPyObject (self : Py T) : PyObject :=
  Internal.Py.mk self.raw .object

unseal Py in
@[ext, grind ext] public theorem ext :
  toPyObject a = toPyObject b → a = b
:= by cases a <;> cases b <;> grind only [toPyObject]

unseal Py in
--@[simp, grind =]
public theorem toPyObject_eq_self :
  (self : Py object).toPyObject = self := by rfl

public instance : ToPyObject (Py T) := ⟨toPyObject⟩

@[simp, grind! .] public theorem toPy_eq_toPyObject :
  toPy (self : Py T) = self.toPyObject := by rfl

public instance : CoeOut (Py T) PyObject := ⟨toPyObject⟩

end Py

unseal Py in
@[inline] public def Internal.Py.Raw.toPyObject (self : Py.Raw) : PyObject :=
  Internal.Py.mk self .object

namespace Internal.Nerodia.PyObject

open Internal

unseal Nerodia.Py in
public noncomputable nonrec def ofModel (o : Py.Model) : PyObject :=
  ⟨.ofModel o, .object⟩

unseal Nerodia.Py in
public noncomputable nonrec def toModel (o : PyObject) : Py.Model :=
  o.raw.toModel

@[simp, grind =]
public theorem toModel_ofModel : toModel (ofModel m) = m := by
  simp [toModel, ofModel]

end Internal.Nerodia.PyObject

/-! ## PyObjectView -/

--/-- Equips {lean}`α` with the dot notation methods of a {lean}`PyObject`. -/
public abbrev PyObjectView (α : Type u) := α

namespace PyObjectView

@[inline] public def toPyObject
  [ToPyObject α] (self : PyObjectView α)
: PyObject := toPy self

@[simp, grind =]
public theorem toPyObject_eq_toPy
  [ToPyObject α] (self : PyObjectView α)
: self.toPyObject = toPy (α := α) self := by rfl

public instance [ToPyObject α] :
  CoeOut (PyObjectView α) PyObject := ⟨toPyObject⟩

end PyObjectView

/-! ## HasType -/

unseal Py in
--/-- Holds if {lean}`self` has the Python typing {lean}`T`. -/
public def PyObject.HasType (T : Typing) (self : PyObject) : Prop :=
  self.raw.HasType T

public section
scoped notation:50 a:51 " ⦂ " T:51 => Nerodia.PyObject.HasType T a
end

recommended_spelling "hasType" for "⦂" in [«term_⦂_»]

/--
{given -show}`o : PyObject, T : Typing`
The typing relation {lean}`o ⦂ T : Prop` asserts that
the Python object {lean}`o` has the Python typing {lean}`T`.
-/
add_decl_doc «term_⦂_»

/--
Holds if {lean}`self` has the Python typing {lean}`T`.
Written as {lean}`self ⦂ T`.
-/
add_decl_doc PyObject.HasType

open Internal in
public def Typing.ofFn (p : PyObject → Prop) : Typing :=
  .ofRawFn fun o => p o.toPyObject

unseal Py in
open Internal in
@[simp, grind =] public theorem Typing.ofFn_iff :
  o ⦂ .ofFn p ↔ p o
:= by
  cases o
  simp [
    Typing.ofFn, PyObject.HasType,
    Py.Raw.HasType.ofRawFn_iff, Py.Raw.toPyObject
  ]

@[deprecated ofFn_iff (since := "2026-09-20")]
public theorem Typing.hasType_ofFn_iff :
  o ⦂ .ofFn p ↔ p o
:= Typing.ofFn_iff

open Internal in
@[ext, grind ext] public theorem Typing.ext
  (h : ∀ o : PyObject, o ⦂ T ↔ o ⦂ U)
: T = U := by
  apply Py.Raw.HasType.ext
  intro o
  specialize h o.toPyObject
  --simp only [Py.toPyObject_eq_self] at h
  simpa [PyObject.HasType, Py.Raw.toPyObject] using h

open Internal in
@[simp, grind .] public theorem PyObject.HasType.object : o ⦂ object :=
  Py.Raw.HasType.object

@[deprecated PyObject.HasType.object (since := "2026-09-22")]
public abbrev Typing.HasType.object := @PyObject.HasType.object

namespace Py

unseal Py in
@[simp, grind! .] public theorem toPyObject_hasType  :
  (self : Py T) ⦂ T := self.raw_hasType

unseal Py in
@[inline] public def ofPyObject (o : PyObject) (h : o ⦂ T) : Py T :=
  Internal.Py.mk o.raw h

unseal Py in
@[simp, grind =] public theorem toPyObject_ofPyObject  :
  toPyObject (ofPyObject o h) = o := by rfl

end Py

/-! ## DecidablePy -/
/--
A typing {lean}`T` with a {lean}`DecidablePy T` instance
has a pure type checking function.
-/
public abbrev DecidablePy (T : Typing) :=
  @DecidablePred PyObject (· ⦂ T)

public instance : DecidablePy object := private_decl%
  (fun _ => isTrue .object)

@[inline, implicit_reducible, expose]
public def Internal.decPy
  (f : PyObject → Bool) (h : ∀ o, f o ↔ o ⦂ T)
: DecidablePy T := fun o =>
  have h := h o
  if fo : f o then
    isTrue (h.mp fo)
  else
    isFalse ((iff_false_left fo).mp h)

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
  eq_py : α = Py T

@[deprecated eq_py (since := "2026-09-20")]
public abbrev ViewPy.isPyT := @ViewPy.eq_py

public instance (priority := low) : ViewPy T (Py T) := ⟨rfl⟩

public instance : ViewPy object PyObject := ⟨rfl⟩

/--
Types {lean}`self` as {lean}`T` using a proof of correctness.

For example, the following pattern in Python:

```
if isinstance(self, T):
  # Python type checkers would assume `self: T` in this block
  doSomethingWithT(self)
else:
  differentType()
```

can be implemented in Lean like so:

{givenInstance -show}`DecidablePy T`
{given -show}`doSomethingWithT : α → IO Unit, differentType : IO Unit`
```leanTerm
if h : self ⦂ T then
  let self := self.attachType h
  doSomethingWithT self
else
  differentType
```
-/
@[inline] public def PyObject.attachType
  [ViewPy T α] (self : PyObject) (h : self ⦂ T)
: α := cast ViewPy.eq_py.symm (.ofPyObject self h)

@[simp, grind =] public theorem PyObject.toPyObject_attachType
  {self : PyObject} {h : self ⦂ T} :
  (self.attachType h).toPyObject = self
:= by simp [attachType]

@[inline] public def Py.attachType
  [ViewPy T α] (self : Py U) (h : self ⦂ T)
: α := self.toPyObject.attachType h

@[simp, grind =] public theorem Py.attachType_spec
  {self : Py U} {h : self ⦂ T} :
  (self.attachType h) = self.toPyObject.attachType h
:= by simp [attachType]

/-! ## NonemptyPy -/

/--
A {lean}`NonemptyPy T` instance provides a proof
that there exists a Python object of type {lean}`T`.
-/
public abbrev NonemptyPy (T : Typing) := Nonempty (Py T)

public theorem NonemptyPy.intro (o : PyObject) (h : o ⦂ T) : NonemptyPy T :=
  ⟨.ofPyObject o h⟩

/-
public theorem NonemptyPy.intro (o : Py.Raw) (h : o ⦂ T) : NonemptyPy T :=
  ⟨⟨o, h⟩⟩
-/

unseal Py in
public instance : NonemptyPy object :=
  ⟨⟨Classical.ofNonempty, .object⟩⟩
