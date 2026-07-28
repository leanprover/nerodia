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

/--
Auxiliary type used for values representing a static Python constant.

Similar to {lean}`Lean.Parser.Category`, definitions of this type have no
content, they simply reserve names that can be coerced into other types (e.g.,
{lean}`TypeExpr` or {lean}`Typing`) via {lean}`CoeDep`.

**Users of Neroida should not define values of this type themselves.**
-/
public structure Constant where
  private mk ::
    private val : NonScalar
    deriving Inhabited

/-! ## Universal Types -/

/-! ### PyObject -/

/--
The ultimate Python base class, [{lit}`object`][1].

[1]: https://docs.python.org/3/library/functions.html#object
-/
public opaque object : Constant

public instance : CoeDep Constant object Typing := ⟨.object⟩

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.object : TypeExpr :=
  ⟨"object"⟩

public instance : CoeDep Constant object TypeExpr := ⟨.object⟩
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

public instance : DecidablePy object := fun _ => isTrue .object

@[inline, implicit_reducible, expose]
public def Internal.decPy
  (f : PyObject → Bool) (h : ∀ o, f o ↔ o.raw ∈ T)
: DecidablePy T := fun o =>
  have h : f (.mk o) ↔ o ∈ T := by
    simpa using h (.mk o)
  if ho :  f (.mk o) then
    isTrue (h.mp ho)
  else
    isFalse ((iff_false_left ho).mp h)

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

As a typing, this is propositionally equivalent to {lean}`object`,
but it has different type class instances.

[1]: https://typing.python.org/en/latest/spec/special-types.html#any
-/
public opaque any : Constant

@[irreducible] public def Typing.any : Typing := .object

public instance : CoeDep Constant any Typing := ⟨.any⟩

@[simp, grind =] public theorem Typing.any_eq_object : any = object := by
  unfold any; rfl

public instance : DecidablePy any := fun _ => isTrue (by simp)

/--
A Python object of unknown type. This is analgous to Python's {lit}`Any`.

As Lean is statically typed, there is little utility in using this type
instead of {name}`PyObject` within Lean code. However, it exists to enable
defining Python functions whose parameters or return should be left untyped.

For example, a module function defined as

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

/-! ### PyNever -/

/--
The special form [{lit}`Never`][1], which is the {lean}`Empty` of Python.

[1]: https://typing.python.org/en/latest/spec/special-types.html#never
-/
public opaque never : Constant

public instance : CoeDep Constant never Typing := ⟨.never⟩
public instance : DecidablePy never := fun _ => isFalse (by simp)

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.never : TypeExpr :=
  ⟨"Never"⟩

public instance : CoeDep Constant never TypeExpr := ⟨.never⟩
public instance : ToTypeExpr never := ⟨never⟩

/--
An instance of the empty type [{lit}`Never`][1]. There are no inhabitants.

[1]: https://docs.python.org/3/library/typing.html#typing.Never
-/
public abbrev PyNever := Py never

/-- Anything holds from an instance of the empty type (c.f., {lean}`Empty.elim`). -/
def PyNever.elim (self : PyNever) : α :=
  Typing.not_mem_never self.raw_mem |>.elim

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
def cast (ty : TypeExpr) (self : Py.Raw) : Py.Raw :=
  .ofModel {self.toModel with hint := ty}

end Py.Raw

open Internal in
/-- The typing for objects weakly typed as {lean}`ty`. -/
def typeHint (ty : TypeExpr) : Typing :=
  .ofFn (·.toModel.hint = ty)

instance : ToTypeExpr (typeHint ty) := ⟨ty⟩

@[simp, grind .] theorem Py.Raw.cast_mem_typeHint :
  Py.Raw.cast ty o ∈ typeHint ty
:= by simp [typeHint, Py.Raw.cast]

instance : NonemptyPy (typeHint ty) :=
  .intro (.cast ty Classical.ofNonempty) Py.Raw.cast_mem_typeHint

@[inherit_doc Py.Raw.cast]
def Py.cast (o : Py T) (ty : TypeExpr) : Py (typeHint ty) :=
  ⟨o.raw.cast ty, Py.Raw.cast_mem_typeHint⟩

/-! ### Buffer -/

/--
The abstract base class [{lit}`Buffer`][1].

[1]: https://docs.python.org/3/library/collections.abc.html#collections.abc.Buffer
-/
public opaque buffer : Constant

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.buffer : TypeExpr :=
  ⟨"Buffer"⟩

public instance : CoeDep Constant buffer TypeExpr := ⟨.buffer⟩

public protected def Typing.buffer : Typing :=
  typeHint buffer
  deriving NonemptyPy

public instance : CoeDep Constant buffer Typing := ⟨.buffer⟩
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

/-- Casts an object into a boffer. No check that this is valid is performed. -/
@[inline] public def PyBuffer.mk (x : PyObject) : PyBuffer := x.cast buffer

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
def Typing.kind (k : Py.Kind) : Typing :=
  .ofFn (·.toModel.kind = k)

@[simp, grind .] theorem Py.Raw.ofKind_mem_kind :
  Py.Raw.ofKind k ∈ Typing.kind k
:= by simp [Typing.kind, Py.Raw.ofKind]

@[simp] theorem Py.Raw.cast_mem_kind_iff :
   o.cast ty ∈ Typing.kind k ↔ o ∈ Typing.kind k
:= by simp [Py.Raw.cast, Typing.kind]

noncomputable instance : Decidable (self ∈ Typing.kind k) :=
  Classical.propDecidable _

open Internal in
noncomputable def Py.Raw.isOfKind (k : Py.Kind) (self : @& Py.Raw) : Bool :=
  self ∈ Typing.kind k

open Classical in
theorem Py.Raw.isOfKind_iff_mem :
  isOfKind k o ↔ o ∈ Typing.kind k
:= Iff.intro of_decide_eq_true decide_eq_true

theorem Typing.Mem.of_isOfKind (h : o.isOfKind k)  : o ∈ kind k :=
  Py.Raw.isOfKind_iff_mem.mp h

theorem NonemptyPy.of_kind : NonemptyPy (.kind k) :=
  .intro (.ofKind k) Py.Raw.ofKind_mem_kind

/-! ### type -/

/--
The ultimate base class of Python types, [{lit}`type`][1].

[1]: https://docs.python.org/3/library/functions.html#type
-/
public opaque type : Constant

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.type : TypeExpr :=
  ⟨"type"⟩

public instance : CoeDep Constant type TypeExpr := ⟨.type⟩

public protected def Typing.type : Typing :=
  .kind .type

public instance : CoeDep Constant type Typing := ⟨.type⟩
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
public opaque baseException : Constant

public protected def Typing.baseException : Typing :=
  .kind .baseException

public instance : CoeDep Constant baseException Typing := ⟨.baseException⟩
public instance : NonemptyPy baseException := .of_kind

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.baseException : TypeExpr :=
  ⟨"BaseException"⟩

public instance : ToTypeExpr baseException := ⟨.baseException⟩

/-- A Python base exception object. That is, an instance of {lit}`BaseException`. -/
public abbrev PyBaseException := PyObjectView <| Py baseException

/-- Shorthand for {lean}`ToPy baseException α` -/
public abbrev ToPyBaseException := ToPy baseException

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
  PyObject.isBaseExceptionInstance o ↔ o.raw ∈ Typing.baseException
:= Py.Raw.isOfKind_iff_mem

public instance : DecidablePy baseException :=
  Internal.decPy (·.isBaseExceptionInstance) (·.isBaseExceptionInstance_iff_mem)

@[inline] public def PyBaseException.mk (o : PyObject) (h : o.isBaseExceptionInstance) : PyBaseException :=
  ⟨o.raw, .of_isOfKind h⟩

/-! ### str -/

/--
The Python string type, [{lit}`str`][1].

[1]: https://docs.python.org/3/library/stdtypes.html#str
-/
public opaque str : Constant

public protected def Typing.str : Typing :=
  .kind .str

public instance : CoeDep Constant str Typing := ⟨.str⟩
public instance : NonemptyPy str := .of_kind

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.str : TypeExpr :=
  ⟨"str"⟩

public instance : CoeDep Constant str TypeExpr := ⟨.str⟩
public instance : ToTypeExpr str := ⟨str⟩

/-- A Python unicode object. That is, an instance of {lit}`str`. -/
public abbrev PyStr := PyObjectView <| Py str

/-- Returns whether this type is an instance of {lit}`str`. -/
@[extern "nerodia_py_object_is_str_instance", view_method]
public def PyObject.isStrInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .str

@[grind _=_] public theorem PyObject.isStrInstance_iff_mem :
  PyObject.isStrInstance o ↔ o.raw ∈ Typing.str
:= Py.Raw.isOfKind_iff_mem

public instance : DecidablePy str :=
  Internal.decPy (·.isStrInstance) (·.isStrInstance_iff_mem)

@[inline] public def PyStr.mk (o : PyObject) (h : o.isStrInstance) : PyStr :=
  ⟨o.raw, .of_isOfKind h⟩

/-! ### bytes -/

/--
The immutable Python byte array type, [{lit}`bytes`][1].

[1]: https://docs.python.org/3/library/stdtypes.html#bytes
-/
public opaque bytes : Constant

public protected def Typing.bytes : Typing :=
  .kind .bytes

public instance : CoeDep Constant bytes Typing := ⟨.bytes⟩
public instance : NonemptyPy bytes := .of_kind

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.bytes : TypeExpr :=
  ⟨"bytes"⟩

public instance : CoeDep Constant bytes TypeExpr := ⟨.bytes⟩
public instance : ToTypeExpr bytes := ⟨bytes⟩

/-- A Python bytes object. That is, an instance of {lit}`bytes`. -/
public abbrev PyBytes := PyBufferView <| PyObjectView <| Py bytes

public instance : ToPyBuffer PyBytes  := ⟨(PyBuffer.mk ·)⟩

/-- Returns whether this type is an instance of {lit}`bytes`. -/
@[extern "nerodia_py_object_is_bytes_instance", view_method]
public def PyObject.isBytesInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .bytes

@[grind _=_] public theorem PyObject.isBytesInstance_iff_mem :
  PyObject.isBytesInstance o ↔ o.raw ∈ Typing.bytes
:= Py.Raw.isOfKind_iff_mem

public instance : DecidablePy bytes :=
  Internal.decPy (·.isBytesInstance) (·.isBytesInstance_iff_mem)

@[inline] public def PyBytes.mk (o : PyObject) (h : o.isBytesInstance) : PyBytes :=
  ⟨o.raw, .of_isOfKind h⟩

/-! ### int -/

/--
The Python integer type, [{lit}`int`][1].

[1]: https://docs.python.org/3/library/functions.html#int
-/
public opaque int : Constant

public protected def Typing.int : Typing :=
  .kind .int

public instance : CoeDep Constant int Typing := ⟨.int⟩
public instance : NonemptyPy int := .of_kind

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.int : TypeExpr :=
  ⟨"int"⟩

public instance : CoeDep Constant int TypeExpr := ⟨.int⟩
public instance : ToTypeExpr int := ⟨int⟩

/-- A Python long object. That is, an instance of {lit}`int`. -/
public abbrev PyInt := PyObjectView <| Py int

/-- Returns whether this type is an instance of {lit}`int`. -/
@[extern "nerodia_py_object_is_int_instance", view_method]
public def PyObject.isIntInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .int

@[grind _=_] public theorem PyObject.isIntInstance_iff_mem :
  PyObject.isIntInstance o ↔ o.raw ∈ Typing.int
:= Py.Raw.isOfKind_iff_mem

public instance : DecidablePy int :=
  Internal.decPy (·.isIntInstance) (·.isIntInstance_iff_mem)

@[inline] public def PyInt.mk (o : PyObject) (h : o.isIntInstance) : PyInt :=
  ⟨o.raw, .of_isOfKind h⟩

/-! ### ModuleType -/

/--
The ultimate base class of Python modules, [{lit}`types.ModuleType`][1].

[1]: https://docs.python.org/3/library/types.html#types.ModuleType
-/
public opaque moduleType : Constant

public protected def Typing.moduleType : Typing :=
  .kind .module

public instance : CoeDep Constant moduleType Typing := ⟨.moduleType⟩
public instance : NonemptyPy moduleType := .of_kind

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.moduleType : TypeExpr :=
  ⟨"ModuleType"⟩

public instance : CoeDep Constant moduleType TypeExpr := ⟨.moduleType⟩
public instance : ToTypeExpr moduleType := ⟨moduleType⟩

/-- A Python module object. That is, an instance of {lit}`types.ModuleType`. -/
public abbrev PyModule := PyObjectView <| Py moduleType

/-- Returns whether this type is an instance of {lit}`types.ModuleType`. -/
@[extern "nerodia_py_object_is_module_instance", view_method]
public def PyObject.isModuleInstance (self : @& PyObject) : Bool :=
  self.raw.isOfKind .module

@[grind _=_] public theorem PyObject.isModuleInstance_iff_mem :
  PyObject.isModuleInstance o ↔ o.raw ∈ Typing.moduleType
:= Py.Raw.isOfKind_iff_mem

public instance : DecidablePy moduleType :=
  Internal.decPy (·.isModuleInstance) (·.isModuleInstance_iff_mem)

@[inline] public def PyModule.mk (o : PyObject) (h : o.isModuleInstance) : PyModule :=
  ⟨o.raw, .of_isOfKind h⟩

/-!
## BaseException Subtypes

Unlike {lit}`BaseException` itself, it is possible to mutate objects between
many of its subtypes (e.g., an object can be retyped to/from {lit}`Exception`).
As such, instances of these subtypes are weakly typed.
-/

open Typing in
instance : NonemptyPy (baseException ∩ typeHint ty) :=
  .intro (.cast ty (.ofKind .baseException)) <| by
    simp [mem_inter_iff_and, Typing.baseException]

/-- The typing for a {lit}`BaseException` weakly typed as {lean}`ty`. -/
def exceptHint (ty : TypeExpr) : Typing :=
  baseException ∩ typeHint ty
  deriving NonemptyPy, IsSubtypeOf baseException, IsSubtypeOf (typeHint ty)

/-! ### Exception -/

/--
The base class of non-exiting Python exceptions, [{lit}`Exception`][1].

[1]: https://docs.python.org/3/library/exceptions.html#Exception
-/
public opaque exception : Constant

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.exception : TypeExpr :=
  ⟨"Exception"⟩

public instance : CoeDep Constant exception TypeExpr := ⟨.exception⟩

public protected def Typing.exception : Typing :=
  exceptHint exception
  deriving NonemptyPy, IsSubtypeOf baseException

public instance : CoeDep Constant exception Typing := ⟨.exception⟩
public instance : ToTypeExpr exception := ⟨exception⟩

/-- A weakly typed instance of {lit}`Exception`. -/
public abbrev PyException := PyBaseExceptionView <| Py exception

/-! ### EOFError -/

/--
The Python end-of-file exception, [{lit}`EOFError`][1].

[1]: https://docs.python.org/3/library/exceptions.html#EOFError
-/
public opaque eofError : Constant

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.eofError : TypeExpr :=
  ⟨"EOFError"⟩

public instance : CoeDep Constant eofError TypeExpr := ⟨.eofError⟩

public protected def Typing.eofError : Typing :=
  exceptHint eofError
  deriving NonemptyPy, IsSubtypeOf baseException

public instance : CoeDep Constant eofError Typing := ⟨.eofError⟩
public instance : ToTypeExpr eofError := ⟨eofError⟩

/-- A weakly typed instance of {lit}`EOFError`. -/
public abbrev PyEOFError := PyBaseExceptionView <| Py eofError

/-! ### SystemError -/

/--
The type of internal Python errors, [{lit}`SystemError`][1].

[1]: https://docs.python.org/3/library/exceptions#SystemError
-/
public opaque systemError : Constant

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.systemError : TypeExpr :=
  ⟨"SystemError"⟩

public instance : CoeDep Constant systemError TypeExpr := ⟨.systemError⟩

public protected def Typing.systemError : Typing :=
  exceptHint systemError
  deriving NonemptyPy, IsSubtypeOf baseException

public instance : CoeDep Constant systemError Typing := ⟨.systemError⟩
public instance : ToTypeExpr systemError := ⟨systemError⟩

/-- A weakly typed instance of {lit}`SystemError`. -/
public abbrev PySystemError := PyBaseExceptionView <| Py systemError

/-! ### TypeError -/

/--
The Python typing exception, [{lit}`TypeError`][1].

[1]: https://docs.python.org/3/library/exceptions#TypeError
-/
public opaque typeError : Constant

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.typeError : TypeExpr :=
  ⟨"TypeError"⟩

public instance : CoeDep Constant typeError TypeExpr := ⟨.typeError⟩

public protected def Typing.typeError : Typing :=
  exceptHint typeError
  deriving NonemptyPy, IsSubtypeOf baseException

public instance : CoeDep Constant typeError Typing := ⟨.typeError⟩
public instance : ToTypeExpr typeError := ⟨typeError⟩

/-- A weakly typed instance of {lit}`TypeError`. -/
public abbrev PyTypeError := PyBaseExceptionView <| Py typeError

/-! ### ValueError -/

/--
The Python exception for invalud values, [{lit}`ValueError`][1].

[1]: https://docs.python.org/3/library/exceptions#ValueError
-/
public opaque valueError : Constant

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.valueError : TypeExpr :=
  ⟨"ValueError"⟩

public instance : CoeDep Constant valueError TypeExpr := ⟨.valueError⟩

public protected def Typing.valueError : Typing :=
  exceptHint valueError
  deriving NonemptyPy, IsSubtypeOf baseException

public instance : CoeDep Constant valueError Typing := ⟨.valueError⟩
public instance : ToTypeExpr valueError := ⟨valueError⟩

/-- A weakly typed instance of {lit}`ValueError`. -/
public abbrev PyValueError := PyBaseExceptionView <| Py valueError

/-! ### RuntimeError -/

/--
The type of generic Python errors, [{lit}`RuntimeError`][1].

[1]: https://docs.python.org/3/library/exceptions#RuntimeError
-/
public opaque runtimeError : Constant

@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.runtimeError : TypeExpr :=
  ⟨"RuntimeError"⟩

public instance : CoeDep Constant runtimeError TypeExpr := ⟨.runtimeError⟩

public protected def Typing.runtimeError : Typing :=
  exceptHint runtimeError
  deriving NonemptyPy, IsSubtypeOf baseException

public instance : CoeDep Constant runtimeError Typing := ⟨.runtimeError⟩
public instance : ToTypeExpr runtimeError := ⟨runtimeError⟩

/-- A weakly typed instance of {lit}`RuntimeError`. -/
public abbrev PyRuntimeError := PyBaseExceptionView <| Py runtimeError
