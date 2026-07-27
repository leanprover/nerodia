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

/--
The ultimate Python base class, [{lit}`object`][1].

[1]: https://docs.python.org/3/library/functions.html#object
-/
@[inline, irreducible, expose] public def object : TypeConst :=
  ⟨"object"⟩

public instance : CoeDep TypeConst object TypePred := ⟨.object⟩
public instance : ToTypeExpr object := ⟨object⟩

/-- Any Python object. That is, an instance of {lit}`object`. -/
public abbrev PyObject := Py object

@[inline] public def PyObject.mk (o : Py.Raw) : PyObject :=
  Py.mk o .object

@[simp, grind =] public theorem PyObject.raw_mk : (mk o).raw = o := by rfl

/-- Shorthand for {lean}`ToPy .object α` -/
public abbrev ToPyObject := ToPy object

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
A special indicator signifying any acceptable value.
This is analgous to Python's [{lit}`Any`][1].

As a type predicate, this is propositionally equivalent to {lean}`object`,
but it has different type class instances.

[1]: https://typing.python.org/en/latest/spec/special-types.html#any
-/
@[irreducible] public def TypePred.any : TypePred := .object

export TypePred (any)

@[simp, grind =] public theorem TypePred.any_eq_object : any = object := by
  unfold any; rfl

/--
A Python object of unknown type. This is analgous to Python's {lit}`Any`.

As Lean is statically typed, there is little utility in using this type
instead of {name}`PyObject` within Lean code. However, it exists to enable
defining Python functions whose parameters or return should be left untyped.

For example, a module funciton defined as

```
@[py_module_fn] def foo (o : PyObject) : PyObject := ...
```

will be given the the type {lit}`(o: object) -> object` by Nerodia, whereas

```
@[py_module_fn] def foo (o : PyAny) : PyAny := ...
```

will have the type {lit}`(o)` with no annotated parameter or return types.
-/
public abbrev PyAny := PyObjectView <| Py any

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
public def typeHint (ty : TypeExpr) : TypePred :=
  .ofFn (·.toModel.hint = ty)

public instance : ToTypeExpr (typeHint ty) := ⟨ty⟩

@[simp, grind .] public theorem Py.Raw.cast_mem_typeHint :
  Py.Raw.cast ty o ∈ typeHint ty
:= by simp [typeHint, Py.Raw.cast]

public instance : NonemptyPy (typeHint ty) :=
  .intro (.cast ty Classical.ofNonempty) Py.Raw.cast_mem_typeHint

@[inherit_doc Py.Raw.cast]
public def Py.cast (o : Py T) (ty : TypeExpr) : Py (typeHint ty) :=
  ⟨o.raw.cast ty, Py.Raw.cast_mem_typeHint⟩

public instance : ToPy (typeHint ty) (Py T)  := ⟨(·.cast ty)⟩

/-! ### Buffer -/

/--
The abstract base class [{lit}`Buffer`][1].

[1]: https://docs.python.org/3/library/collections.abc.html#collections.abc.Buffer
-/
@[inline, irreducible, expose] public def buffer : TypeConst :=
  ⟨"Buffer"⟩

public instance : CoeDep TypeConst buffer TypePred := ⟨typeHint buffer⟩
public instance : ToTypeExpr buffer := ⟨buffer⟩

/--
A weakly typed instance of [{lit}`collections.abc.Buffer`][2].

That is, a Python object which implements the [Buffer Protocol][1].

[1]: https://docs.python.org/3/c-api/buffer.html#bufferobjects
[2]: https://docs.python.org/3/library/collections.abc.html#collections.abc.Buffer
-/
public abbrev PyBuffer := Py buffer

/-- Shorthand for {lean}`ToPy buffer α` -/
public abbrev ToPyBuffer := ToPy buffer

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

/--
The ultimate base class of Python types, [{lit}`type`][1].

[1]: https://docs.python.org/3/library/functions.html#type
-/
@[inline, irreducible, expose] public def type : TypeConst :=
  ⟨"Buffer"⟩

public protected def TypePred.type : TypePred :=
  .kind .type

public instance : CoeDep TypeConst type TypePred := ⟨.type⟩
public instance : NonemptyPy type := .of_kind
public instance : ToTypeExpr type := ⟨type⟩

/--
A Python type object.

An instance of {lit}`type` or one of its subclasses.
Equivalently, a [{lit}`PyTypeObject`][1] pointer managed by Lean.

[1]: https://docs.python.org/3/c-api/type.html#c.PyTypeObject
-/
public abbrev PyType := PyObjectView <| Py type

/-- Returns whether this type is an instance of {lit}`type`. -/
@[extern "nerodia_py_object_is_type_instance", view_method]
public def PyObject.isTypeInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .type

@[inline] public def PyType.mk (o : PyObject) (h : o.isTypeInstance) : PyType :=
  ⟨o.raw, .of_isOfKind h⟩

/-! ### BaseException -/

/--
The ultimate base class of Python excpetions, [{lit}`BaseException`][1].

[1]: https://docs.python.org/3/library/exceptions.html#BaseException
-/
@[inline, irreducible, expose] public def baseException : TypeConst :=
  ⟨"BaseException"⟩

public protected def TypePred.baseException : TypePred :=
  .kind .baseException

public instance : CoeDep TypeConst baseException TypePred := ⟨.baseException⟩
public instance : ToTypeExpr baseException := ⟨baseException⟩
public instance : NonemptyPy baseException := .of_kind

/-- A Python base exception object. That is, an instance of {lit}`BaseException`. -/
public abbrev PyBaseException := PyObjectView <| Py baseException

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

/--
The Python string type, [{lit}`str`][1].

[1]: https://docs.python.org/3/library/stdtypes.html#str
-/
@[inline, irreducible, expose] public def str : TypeConst :=
  ⟨"str"⟩

public protected def TypePred.str : TypePred :=
  .kind .str

public instance : CoeDep TypeConst str TypePred := ⟨.str⟩
public instance : NonemptyPy str := .of_kind
public instance : ToTypeExpr str := ⟨str⟩

/-- A Python unicode object. That is, an instance of {lit}`str`. -/
public abbrev PyStr := PyObjectView <| Py str

/-- Returns whether this type is an instance of {lit}`str`. -/
@[extern "nerodia_py_object_is_str_instance", view_method]
public def PyObject.isStrInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .str

@[inline] public def PyStr.mk (o : PyObject) (h : o.isStrInstance) : PyStr :=
  ⟨o.raw, .of_isOfKind h⟩

/-! ### bytes -/

/--
The immutable Python byte array type, [{lit}`bytes`][1].

[1]: https://docs.python.org/3/library/stdtypes.html#bytes
-/
@[inline, irreducible, expose] public def bytes : TypeConst :=
  ⟨"bytes"⟩

public protected def TypePred.bytes : TypePred :=
  .kind .bytes

public instance : CoeDep TypeConst bytes TypePred := ⟨.bytes⟩
public instance : NonemptyPy bytes := .of_kind
public instance : ToTypeExpr bytes := ⟨bytes⟩

/-- A Python bytes object. That is, an instance of {lit}`bytes`. -/
public abbrev PyBytes := PyBufferView <| PyObjectView <| Py bytes

/-- Returns whether this type is an instance of {lit}`bytes`. -/
@[extern "nerodia_py_object_is_bytes_instance", view_method]
public def PyObject.isBytesInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .bytes

@[inline] public def PyBytes.mk (o : PyObject) (h : o.isBytesInstance) : PyBytes :=
  ⟨o.raw, .of_isOfKind h⟩

/-! ### int -/

/--
The Python integer type, [{lit}`int`][1].

[1]: https://docs.python.org/3/library/functions.html#int
-/
@[inline, irreducible, expose] public def int : TypeConst :=
  ⟨"int"⟩

public protected def TypePred.int : TypePred :=
  .kind .int

public instance : CoeDep TypeConst int TypePred := ⟨.int⟩
public instance : NonemptyPy int := .of_kind
public instance : ToTypeExpr int := ⟨int⟩

/-- A Python long object. That is, an instance of {lit}`int`. -/
public abbrev PyInt := PyObjectView <| Py int

/-- Returns whether this type is an instance of {lit}`int`. -/
@[extern "nerodia_py_object_is_int_instance", view_method]
public def PyObject.isIntInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .int

@[inline] public def PyInt.mk (o : PyObject) (h : o.isIntInstance) : PyInt :=
  ⟨o.raw, .of_isOfKind h⟩

/-! ### ModuleType -/

/--
The ultimate base class of Python modules, [{lit}`types.ModuleType`][1].

[1]: https://docs.python.org/3/library/types.html#types.ModuleType
-/
@[inline, irreducible, expose] public def moduleType : TypeConst :=
  ⟨"ModuleType"⟩

public protected def TypePred.moduleType : TypePred :=
  .kind .module

public instance : CoeDep TypeConst moduleType TypePred := ⟨.moduleType⟩
public instance : ToTypeExpr moduleType := ⟨moduleType⟩
public instance : NonemptyPy moduleType := .of_kind

/-- A Python module object. That is, an instance of {lit}`types.ModuleType`. -/
public abbrev PyModule := PyObjectView <| Py moduleType

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
public instance : NonemptyPy (baseException ∩ typeHint ty) :=
  .intro (.cast ty (.ofKind .baseException)) <| by
    simp [mem_inter_iff_and, TypePred.baseException]

public instance : ToTypeExpr (.baseException ∩ (typeHint ty)) := ⟨ty⟩

/-- Type predicate for a {lit}`BaseException` weakly typed as {lean}`ty`. -/
public def exceptHint (ty : TypeConst) : TypePred :=
  baseException ∩ typeHint ty
  deriving NonemptyPy, IsSubtypeOf baseException, IsSubtypeOf (typeHint ty)

/-! ### Exception -/

/--
The base class of non-exiting Python exceptions, [{lit}`Exception`][1].

[1]: https://docs.python.org/3/library/exceptions.html#Exception
-/
@[inline, irreducible, expose] public def exception : TypeConst :=
  ⟨"Exception"⟩

public instance : CoeDep TypeConst exception TypePred := ⟨exceptHint exception⟩
public instance : ToTypeExpr exception := ⟨exception⟩

/-- A weakly typed instance of {lit}`Exception`. -/
public abbrev PyException := PyBaseExceptionView <| Py exception

/-! ### EOFError -/

/--
The Python end-of-file exception, [{lit}`EOFError`][1].

[1]: https://docs.python.org/3/library/exceptions.html#EOFError
-/
@[inline, irreducible, expose] public def eofError : TypeConst :=
  ⟨"EOFError"⟩

public instance : CoeDep TypeConst eofError TypePred := ⟨exceptHint eofError⟩
public instance : ToTypeExpr eofError := ⟨eofError⟩

/-- A weakly typed instance of {lit}`EOFError`. -/
public abbrev PyEOFError := PyBaseExceptionView <| Py eofError

/-! ### SystemError -/

/--
The type of internal Python errors, [{lit}`SystemError`][1].

[1]: https://docs.python.org/3/library/exceptions#SystemError
-/
@[inline, irreducible, expose] public def systemError : TypeConst :=
  ⟨"SystemError"⟩

public instance : CoeDep TypeConst systemError TypePred := ⟨exceptHint systemError⟩
public instance : ToTypeExpr systemError := ⟨systemError⟩

/-- A weakly typed instance of {lit}`SystemError`. -/
public abbrev PySystemError := PyBaseExceptionView <| Py systemError

/-! ### TypeError -/

/--
The Python typing exception, [{lit}`TypeError`][1].

[1]: https://docs.python.org/3/library/exceptions#TypeError
-/
@[inline, irreducible, expose] public def typeError : TypeConst :=
  ⟨"TypeError"⟩

public instance : CoeDep TypeConst typeError TypePred := ⟨exceptHint typeError⟩
public instance : ToTypeExpr typeError := ⟨typeError⟩

/-- A weakly typed instance of {lit}`TypeError`. -/
public abbrev PyTypeError := PyBaseExceptionView <| Py typeError
