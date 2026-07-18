/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Py.Basic
meta import Nerodia.ViewMethod

/-! # Type Definitions -/

namespace Nerodia

/-! ## Universal Types -/

/-! ### PyObject -/

@[inline, expose] public def TypeExpr.object : TypeExpr :=
  ⟨"object"⟩

public instance : ToTypeExpr .object := ⟨.object⟩

/-- Any Python object. That is, an instance of {lit}`object`. -/
public abbrev PyObject := Py .object

@[inline] public def PyObject.mk (o : Py.Raw) : PyObject :=
  Py.mk o .object

@[simp, grind =] public theorem PyObject.raw_mk : (mk o).raw = o := by rfl

/-- Shorthand for {lean}`ToPy .object α` -/
public abbrev ToPyObject := ToPy .object

namespace ToPyObject

public instance : ToPyObject Py.Raw := ⟨PyObject.mk⟩

@[simp, grind =] public theorem toPy_eq_mk :
  toPy (o : Py.Raw) = PyObject.mk o := by rfl

end ToPyObject

/-- Equips {lean}`α` with the dot notation methods of a {lean}`PyObject`. -/
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

/-! ### PyAny -/

/--
Any Python object.

This is propositionally equivalent to {lean}`object`, but
it has different type class instances.
-/
@[irreducible] public def TypePred.any : TypePred := .object

@[simp, grind =] public theorem TypePred.any_eq_object : any = object := by
  unfold any; rfl

@[simp, grind .] public theorem TypePred.Mem.any : o ∈ any := by
  simp

@[simp, grind .] public theorem TypePred.Subset.any : T ⊆ any := by
  simp

/--
A Python object of unknown type. This is analgous to Python's {lit}`Any`.

In parameters, {lean}`PyObject` should generally be perferred.
{lean}`PyAny` is primarily used to annotate a function that returns
an object of unknown type (e.g., {lit}`Nerodia.import`).
-/
public abbrev PyAny := PyObjectView (Py .any)

@[inline] public def PyAny.mk (o : Py.Raw) : PyAny :=
  Py.mk o .any

@[simp, grind =] public theorem PyAny.raw_mk : (mk o).raw = o := by rfl

/-- Shorthand for {lean}`ToPy .any α` -/
public abbrev ToPyAny := ToPy .any

namespace ToPyAny

public instance : ToPyAny Py.Raw := ⟨PyAny.mk⟩

@[simp, grind =] public theorem toPy_eq_mk :
  toPy (o : Py.Raw) = PyAny.mk o := by rfl

end ToPyAny

/-- Equips {lean}`α` with the dot notation methods of a {lean}`PyObject`. -/
public abbrev PyAnyView (α : Type u) := α

namespace PyAnyView

@[inline] public def toPyAny
  [ToPyAny α] (self : PyAnyView α)
: PyAny := toPy self

@[simp, grind =]
public theorem toPyAny_eq_toPy
  [ToPyAny α] (self : PyAnyView α)
: self.toPyAny = toPy (α := α) self := by rfl

public instance [ToPyAny α] :
  CoeOut (PyAnyView α) PyAny := ⟨toPyAny⟩

end PyAnyView

/-!
## Weak Types

Typing in Python is mutable. Objects can have their type changed by
reassigning their {lit}`__class__` attribute, and types themselves can have
their inheritance tree change by reassigning {lit}`__bases__`.

As such, most type relations in Python do not hold statically and therefore
cannot be modelled correctly and safely by a pure relation in Lean. Nonetheless,
statically typing Python objects in Lean is still useful, so Nerodia provides
a mechanism for *weak typing*. Objects can be freely annotated with *type hints*
in the  form of Python type expressions (i.e., {lean}`TypeExpr`) manually cast
between types without proof.
-/

namespace Py.Raw

set_option linter.unusedVariables.funArgs false in
@[inline] unsafe def castImpl (ty : TypeExpr) (self : Py.Raw) : Py.Raw :=
  unsafeCast self

open Internal in
/--
Casts the object to the type indicating by the expression {lean}`ty`.

This weakly types the object, providing no strong guarantees.

This is akin to the Python {lit}`typing.cast(ty, self)`.
-/
@[implemented_by castImpl]
public def cast (ty : TypeExpr) (self : Py.Raw) : Py.Raw :=
  .ofModel {self.toModel with hint := ty}

end Py.Raw

open Internal in
/-- Type predicate for objects weakly typed as {lean}`ty`. -/
public def TypePred.hint (ty : TypeExpr) : TypePred :=
  .ofFn (·.toModel.hint = ty)

public instance : ToTypeExpr (.hint ty) := ⟨ty⟩

@[simp, grind .] public theorem Py.Raw.cast_mem_hint :
  Py.Raw.cast ty o ∈ TypePred.hint ty
:= by simp [TypePred.hint, Py.Raw.cast]

public instance : NonemptyPy (.hint ty) :=
  .intro (.cast ty Classical.ofNonempty) Py.Raw.cast_mem_hint

/-- A Python object weakly typed as {lean}`ty`.-/
public abbrev HPy (ty : TypeExpr) := Py (.hint ty)

@[inherit_doc Py.Raw.cast]
public def HPy.mk (o : Py.Raw) (ty : TypeExpr) : HPy ty :=
  ⟨o.cast ty, Py.Raw.cast_mem_hint⟩

public instance : ToPy (.hint ty) (Py T)  := ⟨(HPy.mk ·.raw ty)⟩

/-! ### Buffer -/

public def TypeExpr.buffer : TypeExpr := ⟨"Buffer"⟩
public abbrev TypePred.buffer : TypePred := .hint .buffer

/--
A weakly typed instance of [{lit}`collections.abc.Buffer`][2].

That is, a Python object which implements the [Buffer Protocol][1].

[1]: https://docs.python.org/3/c-api/buffer.html#bufferobjects
[2]: https://docs.python.org/3/library/collections.abc.html#collections.abc.Buffer
-/
public abbrev PyBuffer := HPy .buffer

/-- Shorthand for {lean}`ToPy .buffer α` -/
public abbrev ToPyBuffer := ToPy .buffer

/-- Equips {lean}`α` with the dot notation methods of a {lean}`PyBuffer`. -/
public abbrev PyBufferView (α : Type u) := α

namespace PyBufferView

@[inline] public def toPyBuffer
  [ToPyBuffer α] (self : PyBufferView α)
: PyBuffer := toPy self

@[simp, grind =]
public theorem toPyBuffer_eq_toPy
  [ToPyBuffer α] (self : PyBufferView α)
: self.toPyBuffer = toPy (α := α) self := by rfl

public instance [ToPyBuffer α] :
  CoeOut (PyBufferView α) PyBuffer := ⟨toPyBuffer⟩

end PyBufferView

/-!
## Strong Types

Not all typing in Nerodia is weak. While the Python specification leaves
the mutability of an object's type undefined, the CPython implementation has
notable restrictions on this mutablility. Notably, it prevents reassignment
between many builtin types (e.g., {lit}`str`).

Nerodia lverages this provide pure type checks (e.g., {lit}`isStrInstance`)
for these functions. Their static types (e.g., {lit}`PyStr`) then hold a proof
of this check. Since many builtin types are also immutable, the data of such
types can be safely accessed in a pure manner (e.g., {lit}`PyStr.toString`).

Nonethless, there are caveats. Foremost, this is not strictly in accordance
with the Python specification, which leaves the mutability of an object's type
undefined. However, CPython's implementation strongly assumes confusion between
builtin types cannot happen (e.g., retyping an {lit}`int` to/from a {lit}`str`
would easily segfault when used). Weighing these considerations, Nerodia chooses
to model builtin types functionally to make reasoning easier and more pure,
accepting the cost of a potential future breakage in the event of an unlikely,
massive Python refactor.
-/

open Internal in
noncomputable def Py.Raw.ofKind (k : Py.Kind) : Py.Raw :=
  .ofModel {Classical.ofNonempty (α := Py.Model) with kind := k}

open Internal in
def TypePred.kind (k : Py.Kind) : TypePred :=
  .ofFn (·.toModel.kind = k)

@[simp, grind .] theorem Py.Raw.ofKind_mem_kind :
  Py.Raw.ofKind k ∈ TypePred.kind k
:= by simp [TypePred.kind, Py.Raw.ofKind]

@[simp] theorem Py.Raw.cast_mem_kind_iff :
   o.cast ty ∈ TypePred.kind k ↔ o ∈ TypePred.kind k
:= by simp [Py.Raw.cast, TypePred.kind]

noncomputable instance : Decidable (self ∈ TypePred.kind k) :=
  Classical.propDecidable _

open Internal in
noncomputable def Py.Raw.isOfKind (k : Py.Kind) (self : @& Py.Raw) : Bool :=
  self ∈ TypePred.kind k

open Classical in
theorem Py.Raw.isOfKind_iff_mem :
  isOfKind k o ↔ o ∈ TypePred.kind k
:= Iff.intro of_decide_eq_true decide_eq_true

theorem TypePred.Mem.of_isOfKind (h : o.isOfKind k)  : o ∈ kind k :=
  Py.Raw.isOfKind_iff_mem.mp h

theorem NonemptyPy.of_kind : NonemptyPy (.kind k) :=
  .intro (.ofKind k) Py.Raw.ofKind_mem_kind

/-! ### type -/

public def TypePred.type : TypePred :=
  .kind .type

public instance : NonemptyPy .type := .of_kind

/--
A Python type object.

An instance of {lit}`type` or one of its subclasses.
Equivalently, a [{lit}`PyTypeObject`][1] pointer managed by Lean.

[1]: https://docs.python.org/3/c-api/type.html#c.PyTypeObject
-/
public abbrev PyType := PyObjectView <| Py .type

/-- Returns whether this type is an instance of {lit}`type`. -/
@[extern "nerodia_py_object_is_type_instance", view_method]
public def PyObject.isTypeInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .type

@[inline] public def PyType.mk (o : PyObject) (h : o.isTypeInstance) : PyType :=
  ⟨o.raw, .of_isOfKind h⟩

/-! ### BaseException -/

public def TypePred.baseException : TypePred :=
  .kind .baseException

public instance : NonemptyPy .baseException := .of_kind

@[inline, expose] public def TypeExpr.baseException : TypeExpr :=
  ⟨"BaseException"⟩

public instance : ToTypeExpr .baseException := ⟨.baseException⟩

/-- A Python base exception object. That is, an instance of {lit}`BaseException`. -/
public abbrev PyBaseException := PyObjectView <| Py .baseException

/-- Shorthand for {lean}`ToPy .baseException α` -/
public abbrev ToPyBaseException := ToPy .baseException

/-- Equips {lean}`α` with the dot notation methods of a {lean}`PyBaseException`. -/
public abbrev PyBaseExceptionView (α : Type u) := α

namespace PyBaseExceptionView

@[inline] public def toPyBaseException
  [ToPyBaseException α] (self : PyBaseExceptionView α)
: PyBaseException := toPy self

@[simp, grind =]
public theorem toPyBaseException_eq_toPy
  [ToPyBaseException α] (self : PyBaseExceptionView α)
: self.toPyBaseException = toPy (α := α) self := by rfl

public instance [ToPyBaseException α] :
  CoeOut (PyBaseExceptionView α) PyBaseException := ⟨toPyBaseException⟩

end PyBaseExceptionView

/-- Returns whether this type is an instance of {lit}`BaseException`. -/
@[extern "nerodia_py_object_is_base_exception_instance", view_method]
public def PyObject.isBaseExceptionInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .baseException

@[grind _=_] public theorem PyObject.isBaseExceptionInstance_iff_mem :
  PyObject.isBaseExceptionInstance o ↔ o.raw ∈ TypePred.baseException
:= Py.Raw.isOfKind_iff_mem

@[inline] public def PyBaseException.mk (o : PyObject) (h : o.isBaseExceptionInstance) : PyBaseException :=
  ⟨o.raw, .of_isOfKind h⟩

/-! ### str -/

public def TypePred.str : TypePred :=
  .kind .str

public instance : NonemptyPy .str := .of_kind

@[inline, expose] public def TypeExpr.str : TypeExpr :=
  ⟨"str"⟩

public instance : ToTypeExpr .str := ⟨.str⟩

/-- A Python unicode object. That is, an instance of {lit}`str`. -/
public abbrev PyStr := PyObjectView <| Py .str

/-- Returns whether this type is an instance of {lit}`str`. -/
@[extern "nerodia_py_object_is_str_instance", view_method]
public def PyObject.isStrInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .str

@[inline] public def PyStr.mk (o : PyObject) (h : o.isStrInstance) : PyStr :=
  ⟨o.raw, .of_isOfKind h⟩

/-! ### bytes -/

public def TypePred.bytes : TypePred :=
  .kind .bytes

public instance : NonemptyPy .bytes := .of_kind

@[inline, expose] public def TypeExpr.bytes : TypeExpr :=
  ⟨"str"⟩

public instance : ToTypeExpr .bytes := ⟨.bytes⟩

/-- A Python bytes object. That is, an instance of {lit}`bytes`. -/
public abbrev PyBytes := PyBufferView <| PyObjectView <| Py .bytes

/-- Returns whether this type is an instance of {lit}`bytes`. -/
@[extern "nerodia_py_object_is_bytes_instance", view_method]
public def PyObject.isBytesInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .bytes

@[inline] public def PyBytes.mk (o : PyObject) (h : o.isBytesInstance) : PyBytes :=
  ⟨o.raw, .of_isOfKind h⟩

/-! ### types.ModuleType -/

public def TypePred.module : TypePred :=
  .kind .module

public instance : NonemptyPy .module := .of_kind

/-- A Python module object. That is, an instance of {lit}`types.ModuleType`. -/
public abbrev PyModule := PyObjectView <| Py .module

/-- Returns whether this type is an instance of {lit}`types.ModuleType`. -/
@[extern "nerodia_py_object_is_module_instance", view_method]
public def PyObject.isModuleInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .module

@[inline] public def PyModule.mk (o : PyObject) (h : o.isModuleInstance) : PyModule :=
  ⟨o.raw, .of_isOfKind h⟩

/-!
## BaseException Subtypes

Unlike {lit}`BaseException` itself, it is possible to mutate objects between
many of its subtypes (e.g., an object can be retyped to/from {lit}`Exception`).
As such, instances of these subtypes are weakly typed.
-/

open TypePred in
public instance : NonemptyPy (.baseException ∩ .hint ty) :=
  .intro (.cast ty (.ofKind .baseException)) <| by
    simp [mem_inter_iff_and, baseException]

public instance : ToTypeExpr (.baseException ∩ (.hint ty)) := ⟨ty⟩

/-- An instance of {lit}`BaseException` that is weakly typed as {lit}`ty`. -/
public abbrev HPyBaseException (ty : TypeExpr) :=
  PyBaseExceptionView <| Py <| .baseException ∩ .hint ty

/-! ### Exception -/

public def TypeExpr.exception : TypeExpr := ⟨"Exception"⟩

public abbrev TypePred.exception : TypePred :=
  baseException ∩ hint .exception

/-- A weakly typed instance of {lit}`Exception`. -/
public abbrev PyException := HPyBaseException .exception

/-! ### SystemError -/

public def TypeExpr.systemError : TypeExpr := ⟨"SystemError"⟩

public abbrev TypePred.systemError : TypePred :=
  baseException ∩ hint .systemError

/-- A weakly typed instance of {lit}`SystemError`. -/
public abbrev PySystemError := HPyBaseException .systemError

/-! ### TypeError -/

public def TypeExpr.typeError : TypeExpr := ⟨"TypeError"⟩

public abbrev TypePred.typeError : TypePred :=
  baseException ∩ hint .typeError

/-- A weakly typed instance of {lit}`TypeError`. -/
public abbrev PyTypeError := HPyBaseException .typeError
