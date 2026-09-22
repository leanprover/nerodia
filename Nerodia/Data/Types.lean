/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.PyAny
public import Nerodia.Data.PyNever
public import Nerodia.Data.Typing.Ops
public import Nerodia.Data.Typing.Promotable
meta import Nerodia.Internal.ViewMethod

/-! # Type Definitions -/

namespace Nerodia

/-!
## Weak Types

Typing in Python is mutable. Objects can have their type changed by
reassigning their {lit}`__class__` attribute, and types themselves can have
their inheritance tree change by reassigning {lit}`__bases__`.

As such, most type relations in Python do not hold statically and therefore
cannot be modelled correctly and safely by a pure {lean}`Typing` in Lean.
Nonetheless, statically typing Python objects in Lean is still useful, so
Nerodia provides a mechanism for _weak typing_. Objects are annotated
with erased _type hints_ to indicate the expected type and the
{lean}`Typing` of weak types checks for these type hints.
-/

namespace PyObject

set_option linter.unusedVariables.funArgs false in
@[inline] unsafe def withTypeHintImpl (ty : TypeExpr) (self : PyObject) : PyObject :=
  unsafeCast self

open Internal in
/--
Casts the object to the type indicating by the expression {lean}`ty`.

This weakly types the object, providing no strong guarantees.

This is akin to the Python {lit}`typing.cast(ty, self)`.
-/
@[implemented_by withTypeHintImpl]
def withTypeHint (ty : TypeExpr) (self : PyObject) : PyObject :=
  .ofModel {self.toModel with hint := ty}

end PyObject

open Internal in
/-- The typing for objects weakly typed as {lean}`ty`. -/
def typeHint (ty : TypeExpr) : Typing :=
  .ofFn (·.toModel.hint = ty)

instance : ToTypeExpr (typeHint ty) := ⟨ty⟩

@[simp, grind .] theorem PyObject.withTypeHint_hasType_typeHint :
  withTypeHint ty o ⦂ typeHint ty
:= by simp [typeHint, PyObject.withTypeHint]

instance : NonemptyPy (typeHint ty) :=
  ⟨.ofPyObject (.withTypeHint ty Classical.ofNonempty) PyObject.withTypeHint_hasType_typeHint⟩

@[inherit_doc PyObject.withTypeHint]
nonrec def Py.cast (o : Py T) (ty : TypeExpr) : Py (typeHint ty) :=
  .ofPyObject (o.toPyObject.withTypeHint ty) PyObject.withTypeHint_hasType_typeHint

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

public instance : ViewPy buffer PyBuffer := ⟨rfl⟩

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

/-- Casts an object into a buffer. No check that this is valid is performed. -/
@[inline] public def Internal.mkPyBuffer (x : PyObject) : PyBuffer := x.cast buffer

/-!
## Strong Types

While the Python specification leaves the mutability of an object's type
undefined, the CPython implementation places notable restrictions on this
mutability.  Notably, it prevents reassignment between many builtin types
(e.g., {lit}`str`).

Nerodia leverages this to provide pure type checks (e.g., {lit}`x ⦂ str`) for
such types. Their static types (e.g., {lit}`PyStr`) then hold a proof
of this check. Since many builtin types are also immutable, the data of such
types can be safely accessed in a pure manner (e.g., {lit}`PyStr.toString`).

Still, there are caveats. Foremost, this is not strictly in accordance with the
Python specification, which leaves the mutability of an object's type undefined.
However, CPython's implementation strongly assumes confusion between builtin
types cannot happen (e.g., retyping an {lit}`int` to/from a {lit}`str` would
easily segfault when used). Weighing these considerations, Nerodia chooses to
model builtin types functionally to make reasoning easier and more pure,
accepting the cost of a potential future breakage in the event of an unlikely,
massive CPython refactor.
-/

open Internal in
def Typing.kind (k : Py.Kind) : Typing :=
  .ofFn (·.toModel.kind = k)

open Internal in
noncomputable def PyObject.ofKind (k : Py.Kind) : PyObject :=
  .ofModel {Classical.ofNonempty (α := Py.Model) with kind := k}

@[simp, grind .] theorem PyObject.ofKind_hasType_kind :
  .ofKind k ⦂ .kind k
:= by simp [Typing.kind, PyObject.ofKind]

instance : NonemptyPy (.kind k) :=
  ⟨.ofPyObject (.ofKind k) PyObject.ofKind_hasType_kind⟩

@[simp] theorem PyObject.withTypeHint_hasType_kind_iff :
   o.withTypeHint ty ⦂ .kind k ↔ o ⦂ .kind k
:= by simp [PyObject.withTypeHint, Typing.kind]

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
  deriving NonemptyPy

public instance : CoeDep Constant type Typing := ⟨.type⟩
public instance : ToTypeExpr type := ⟨type⟩

/--
A Python type object.

An instance of {lit}`type` or one of its subclasses.
Equivalently, a [{lit}`PyTypeObject`][1] pointer managed by Lean.

[1]: https://docs.python.org/3/c-api/type.html#c.PyTypeObject
-/
public abbrev PyType := PyObjectView <| Py type

public instance : ViewPy type PyType := ⟨rfl⟩

/-! ### BaseException -/

/--
The ultimate base class of Python exceptions, [{lit}`BaseException`][1].

[1]: https://docs.python.org/3/library/exceptions.html#BaseException
-/
public opaque baseException : Constant

@[inherit_doc baseException]
public protected def Typing.baseException : Typing :=
  .kind .baseException
  deriving NonemptyPy

public instance : CoeDep Constant baseException Typing := ⟨.baseException⟩

@[inherit_doc baseException, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.baseException : TypeExpr :=
  ⟨"BaseException"⟩

public instance : ToTypeExpr baseException := ⟨.baseException⟩

/-- A Python base exception object. That is, an instance of {lit}`BaseException`. -/
public abbrev PyBaseException := PyObjectView <| Py baseException

public instance : ViewPy baseException PyBaseException := ⟨rfl⟩

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

/-! ### str -/

/--
The Python string type, [{lit}`str`][1].

[1]: https://docs.python.org/3/library/stdtypes.html#str
-/
public opaque str : Constant

@[inherit_doc str]
public protected def Typing.str : Typing :=
  .kind .str
  deriving NonemptyPy

public instance : CoeDep Constant str Typing := ⟨.str⟩

@[inherit_doc str, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.str : TypeExpr :=
  ⟨"str"⟩

public instance : CoeDep Constant str TypeExpr := ⟨.str⟩
public instance : ToTypeExpr str := ⟨str⟩

/-- A Python unicode object. That is, an instance of {lit}`str`. -/
public abbrev PyStr := PyObjectView <| Py str

public instance : ViewPy str PyStr := ⟨rfl⟩

/-! ### bytes -/

/--
The immutable Python byte array type, [{lit}`bytes`][1].

[1]: https://docs.python.org/3/library/stdtypes.html#bytes
-/
public opaque bytes : Constant

@[inherit_doc bytes]
public protected def Typing.bytes : Typing :=
  .kind .bytes
  deriving NonemptyPy

public instance : CoeDep Constant bytes Typing := ⟨.bytes⟩

@[inherit_doc bytes, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.bytes : TypeExpr :=
  ⟨"bytes"⟩

public instance : CoeDep Constant bytes TypeExpr := ⟨.bytes⟩
public instance : ToTypeExpr bytes := ⟨bytes⟩

/-- A Python bytes object. That is, an instance of {lit}`bytes`. -/
public abbrev PyBytes := PyBufferView <| PyObjectView <| Py bytes

public instance : ViewPy bytes PyBytes := ⟨rfl⟩

public instance : ToPyBuffer PyBytes where
  toPy o := private Internal.mkPyBuffer o

open Classical in
/-- Returns whether {lean}`self` is an instance of {lit}`bytes`. -/
@[extern "nerodia_py_object_is_bytes_instance"]
def PyObject.isBytesInstance (self : @& PyObject) : Bool :=
  self ⦂ bytes

open PyObject in
public instance : DecidablePy bytes := private_decl%
  (Internal.decPy isBytesInstance (by simp [isBytesInstance]))

/-! ### int -/

/--
The Python integer type, [{lit}`int`][1].

[1]: https://docs.python.org/3/library/functions.html#int
-/
public opaque int : Constant

@[inherit_doc int]
public protected def Typing.int : Typing :=
  .kind .int
  deriving NonemptyPy

public instance : CoeDep Constant int Typing := ⟨.int⟩

@[inherit_doc int, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.int : TypeExpr :=
  ⟨"int"⟩

public instance : CoeDep Constant int TypeExpr := ⟨.int⟩
public instance : ToTypeExpr int := ⟨int⟩

/-- A Python long object. That is, an instance of {lit}`int`. -/
public abbrev PyInt := PyObjectView <| Py int

public instance : ViewPy int PyInt := ⟨rfl⟩

/-! ### ModuleType -/

/--
The ultimate base class of Python modules, [{lit}`types.ModuleType`][1].

[1]: https://docs.python.org/3/library/types.html#types.ModuleType
-/
public opaque moduleType : Constant

@[inherit_doc moduleType]
public protected def Typing.moduleType : Typing :=
  .kind .module
  deriving NonemptyPy

public instance : CoeDep Constant moduleType Typing := ⟨.moduleType⟩

@[inherit_doc moduleType, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.moduleType : TypeExpr :=
  ⟨"ModuleType"⟩

public instance : CoeDep Constant moduleType TypeExpr := ⟨.moduleType⟩
public instance : ToTypeExpr moduleType := ⟨moduleType⟩

/-- A Python module object. That is, an instance of {lit}`types.ModuleType`. -/
public abbrev PyModule := PyObjectView <| Py moduleType

public instance : ViewPy moduleType PyModule := ⟨rfl⟩

/-! ### None -/

/--
The Python boolean literal, [{lit}`None`][1].

[1]: https://docs.python.org/3/builtins/constants.html#None
-/
@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.none : TypeExpr :=
  ⟨"None"⟩

public instance : CoeDep (Option α) none TypeExpr := ⟨.none⟩

noncomputable opaque PyEnvironment.noneAddr (env : PyEnvironment) : Addr

open Internal in
noncomputable def PyEnvironment.noneObj (env : @& PyEnvironment) : PyObject :=
  .ofModel {env, addr := env.noneAddr, hint := .none}

open Internal in
@[inherit_doc TypeExpr.none]
public protected def Typing.none : Typing :=
  ofFn fun o => o.toModel.toInnerModel = o.toModel.env.noneObj.toModel.toInnerModel

public instance : CoeDep (Option α) none Typing := ⟨.none⟩
public instance : ToTypeExpr none := ⟨none⟩

theorem PyEnvironment.noneObj_hasType {env} : noneObj env ⦂ none := by
  simp [PyEnvironment.noneObj, Typing.none]

/-- A Python {lit}`None` constant. -/
public abbrev PyNone := PyObjectView <| Py none

public instance : ViewPy none PyNone := ⟨rfl⟩

public noncomputable def Internal.Nerodia.PyEnvironment.noneCore (env : @& PyEnvironment) : PyNone :=
  .ofPyObject env.noneObj env.noneObj_hasType

public instance : NonemptyPy none :=
  ⟨Internal.Nerodia.PyEnvironment.noneCore Classical.ofNonempty⟩

public def Typing.optional (T : Typing) : Typing :=
  T ∪ none
  deriving NonemptyPy

@[simp, grind _=_] public theorem Typing.optional_eq_union_none :
  optional T = T ∪ none := by rfl

public instance : PromotableRtl (T ∪ none) (.optional T) := ⟨by rfl⟩
public instance : PromotableLtr (.optional T) (T ∪ none) := ⟨by rfl⟩

public instance [ToTypeExpr T] : ToTypeExpr (.optional T) where
  toTypeExpr := .optional (ToTypeExpr.toTypeExpr T)

/-! ### bool -/

/-- Equips {lean}`α` with the dot notation methods of a {lean}`PyObject`. -/
public abbrev PyBoolView (α : Type u) := α

/-! ### False -/

/--
The Python boolean literal, [{lit}`False`][1].

[1]: https://docs.python.org/3/builtins/constants.html#False
-/
@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.false : TypeExpr :=
  ⟨"Literal[False]"⟩

public instance : CoeDep Bool false TypeExpr := ⟨.false⟩

noncomputable opaque PyEnvironment.falseAddr (env : PyEnvironment) : Addr

open Internal in
noncomputable def PyEnvironment.falseObj (env : @& PyEnvironment) : PyObject :=
  .ofModel {env, addr := env.falseAddr, kind := .int, hint := .false}

open Internal in
@[inherit_doc TypeExpr.false]
public protected def Typing.false : Typing :=
  ofFn fun o => o.toModel.toInnerModel = o.toModel.env.falseObj.toModel.toInnerModel

public instance : CoeDep Bool false Typing := ⟨.false⟩
public instance : ToTypeExpr false := ⟨false⟩

theorem PyEnvironment.falseObj_hasType {env} : falseObj env ⦂ false := by
  simp [PyEnvironment.falseObj, Typing.false]

/-- A Python {lit}`False` constant. -/
public abbrev PyFalse := PyBoolView <| PyObjectView <| Py false

public instance : ViewPy false PyFalse := ⟨rfl⟩

public noncomputable def Internal.Nerodia.PyEnvironment.falseCore (env : @& PyEnvironment) : PyFalse :=
  .ofPyObject env.falseObj env.falseObj_hasType

public instance : NonemptyPy false :=
  ⟨Internal.Nerodia.PyEnvironment.falseCore Classical.ofNonempty⟩

/-! ## True -/

/--
The Python boolean literal, [{lit}`True`][1].

[1]: https://docs.python.org/3/builtins/constants.html#True
-/
@[inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.true : TypeExpr :=
  ⟨"Literal[True]"⟩

public instance : CoeDep Bool true TypeExpr := ⟨.true⟩

noncomputable opaque PyEnvironment.trueAddr (env : PyEnvironment) : Addr

open Internal in
noncomputable def PyEnvironment.trueObj (env : @& PyEnvironment) : PyObject :=
  .ofModel {env, addr := env.trueAddr, kind := .int, hint := .true}

open Internal in
@[inherit_doc TypeExpr.true]
public protected def Typing.true : Typing :=
  ofFn fun o => o.toModel.toInnerModel = o.toModel.env.trueObj.toModel.toInnerModel

public instance : CoeDep Bool true Typing := ⟨.true⟩
public instance : ToTypeExpr true := ⟨true⟩

theorem PyEnvironment.trueObj_hasType {env} : trueObj env ⦂ true := by
  simp [PyEnvironment.trueObj, Typing.true]

/-- A Python {lit}`True` constant. -/
public abbrev PyTrue := PyBoolView <| PyObjectView <| Py true

public instance : ViewPy true PyTrue := ⟨rfl⟩

public noncomputable def Internal.Nerodia.PyEnvironment.trueCore (env : @& PyEnvironment) : PyTrue :=
  .ofPyObject env.trueObj env.trueObj_hasType

public instance : NonemptyPy true :=
  ⟨Internal.Nerodia.PyEnvironment.trueCore Classical.ofNonempty⟩

/-! ## bool -/

/--
The Python boolean type, [{lit}`bool`][1].

[1]: https://docs.python.org/3/library/functions.html#bool
-/
public opaque bool : Constant

@[inherit_doc bool, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.bool : TypeExpr :=
  ⟨"bool"⟩

public instance : CoeDep Constant bool TypeExpr := ⟨.bool⟩

open Internal in
@[inherit_doc bool]
public protected def Typing.bool : Typing :=
  false ∪ true
  deriving NonemptyPy

public instance : CoeDep Constant bool Typing := ⟨.bool⟩
public instance : ToTypeExpr bool := ⟨bool⟩

@[grind _=_] public theorem bool_eq_false_union_true :
  Typing.bool = .false ∪ .true := by rfl

theorem false_subset_bool : Typing.false ⊆ bool := by
  simp [bool_eq_false_union_true, Typing.Subset.union_left]

public instance : PromotableB bool false := ⟨false_subset_bool⟩

theorem true_subset_bool : Typing.true ⊆ bool := by
  simp [bool_eq_false_union_true, Typing.Subset.union_right]

public instance : PromotableB bool true := ⟨true_subset_bool⟩

open Typing PyEnvironment Internal Nerodia in
theorem bool_subset_int : Typing.bool ⊆ int := by
  simp only [bool_eq_false_union_true, subset_iff_forall, union_iff_or]
  intro o
  simp only [Typing.int, Typing.false, Typing.true, kind, ofFn_iff]
  simp only [falseObj, trueObj, PyObject.toModel_ofModel]
  rintro (h | h) <;> rw [h]

public instance : PromotableB int bool := ⟨bool_subset_int⟩

/-- A Python boolean object. That is, an instance of {lit}`bool`. -/
public abbrev PyBool := PyObjectView <| Py bool

public instance : ViewPy bool PyBool := ⟨rfl⟩

/-- Shorthand for {lean}`ToPy bool α` -/
public abbrev ToPyBool := ToPy bool

namespace PyBoolView

@[inline] public def toPyBool
  [ToPyBool α] (self : PyBoolView α)
: PyBool := toPy self

@[simp, grind =]
public theorem toPyObject_eq_toPy
  [ToPyBool α] (self : PyBoolView α)
: self.toPyBool = toPy (α := α) self := by rfl

public instance [ToPyBool α] :
  CoeOut (PyBoolView α) PyBool := ⟨toPyBool⟩

end PyBoolView

/-!
## BaseException Subtypes

Unlike {lit}`BaseException` itself, it is possible to mutate objects between
many of its subtypes (e.g., an object can be retyped to/from {lit}`Exception`).
As such, instances of these subtypes are weakly typed.
-/

open Typing in
instance : NonemptyPy (baseException ∩ typeHint ty) :=
  .intro (.withTypeHint ty (.ofKind .baseException)) <| by
    simp [inter_iff_and, Typing.baseException]

/-- The typing for a {lit}`BaseException` weakly typed as {lean}`ty`. -/
def exceptHint (ty : TypeExpr) : Typing :=
  baseException ∩ typeHint ty
  deriving NonemptyPy, PromotableRtl baseException, PromotableRtl (typeHint ty)

/-! ### Exception -/

/--
The base class of non-exiting Python exceptions, [{lit}`Exception`][1].

[1]: https://docs.python.org/3/library/exceptions.html#Exception
-/
public opaque exception : Constant

@[inherit_doc exception, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.exception : TypeExpr :=
  ⟨"Exception"⟩

public instance : CoeDep Constant exception TypeExpr := ⟨.exception⟩

@[inherit_doc exception]
public protected def Typing.exception : Typing :=
  exceptHint exception
  deriving NonemptyPy

public instance : CoeDep Constant exception Typing := ⟨.exception⟩
public instance : ToTypeExpr exception := ⟨exception⟩

public instance : PromotableB baseException exception :=
  ⟨Promotable.infer (U := exceptHint _)⟩

/-- A weakly typed instance of {lit}`Exception`. -/
public abbrev PyException := PyBaseExceptionView <| PyObjectView <| Py exception

public instance : ViewPy exception PyException := ⟨rfl⟩

/-! ### EOFError -/

/--
The Python end-of-file exception, [{lit}`EOFError`][1].

[1]: https://docs.python.org/3/library/exceptions.html#EOFError
-/
public opaque eofError : Constant

@[inherit_doc eofError, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.eofError : TypeExpr :=
  ⟨"EOFError"⟩

public instance : CoeDep Constant eofError TypeExpr := ⟨.eofError⟩

@[inherit_doc eofError]
public protected def Typing.eofError : Typing :=
  exceptHint eofError
  deriving NonemptyPy

public instance : CoeDep Constant eofError Typing := ⟨.eofError⟩
public instance : ToTypeExpr eofError := ⟨eofError⟩

public instance : PromotableB baseException eofError :=
  ⟨Promotable.infer (U := exceptHint _)⟩

/-- A weakly typed instance of {lit}`EOFError`. -/
public abbrev PyEOFError := PyBaseExceptionView <| PyObjectView <| Py eofError

public instance : ViewPy eofError PyEOFError := ⟨rfl⟩

/-! ### OSError -/

/--
The Python type of native errors, [{lit}`OSError`][1].

[1]: https://docs.python.org/3/library/exceptions.html#OSError
-/
public opaque osError : Constant

@[inherit_doc osError, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.osError : TypeExpr :=
  ⟨"OSError"⟩

public instance : CoeDep Constant osError TypeExpr := ⟨.osError⟩

@[inherit_doc osError]
public protected def Typing.osError : Typing :=
  exceptHint osError
  deriving NonemptyPy

public instance : CoeDep Constant osError Typing := ⟨.osError⟩
public instance : ToTypeExpr osError := ⟨osError⟩

public instance : PromotableB baseException osError :=
  ⟨Promotable.infer (U := exceptHint _)⟩

/-- A weakly typed instance of {lit}`OSError`. -/
public abbrev PyOSError := PyBaseExceptionView <| PyObjectView <| Py osError

public instance : ViewPy osError PyOSError := ⟨rfl⟩

/-! ### SystemError -/

/--
The type of internal Python errors, [{lit}`SystemError`][1].

[1]: https://docs.python.org/3/library/exceptions#SystemError
-/
public opaque systemError : Constant

@[inherit_doc systemError, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.systemError : TypeExpr :=
  ⟨"SystemError"⟩

public instance : CoeDep Constant systemError TypeExpr := ⟨.systemError⟩

@[inherit_doc systemError]
public protected def Typing.systemError : Typing :=
  exceptHint systemError
  deriving NonemptyPy

public instance : CoeDep Constant systemError Typing := ⟨.systemError⟩
public instance : ToTypeExpr systemError := ⟨systemError⟩

public instance : PromotableB baseException systemError :=
  ⟨Promotable.infer (U := exceptHint _)⟩

/-- A weakly typed instance of {lit}`SystemError`. -/
public abbrev PySystemError := PyBaseExceptionView <| PyObjectView <| Py systemError

public instance : ViewPy systemError PySystemError := ⟨rfl⟩

/-! ### TypeError -/

/--
The Python typing exception, [{lit}`TypeError`][1].

[1]: https://docs.python.org/3/library/exceptions#TypeError
-/
public opaque typeError : Constant

@[inherit_doc typeError, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.typeError : TypeExpr :=
  ⟨"TypeError"⟩

public instance : CoeDep Constant typeError TypeExpr := ⟨.typeError⟩

@[inherit_doc typeError]
public protected def Typing.typeError : Typing :=
  exceptHint typeError
  deriving NonemptyPy

public instance : CoeDep Constant typeError Typing := ⟨.typeError⟩
public instance : ToTypeExpr typeError := ⟨typeError⟩

public instance : PromotableB baseException typeError :=
  ⟨Promotable.infer (U := exceptHint _)⟩

/-- A weakly typed instance of {lit}`TypeError`. -/
public abbrev PyTypeError := PyBaseExceptionView <| PyObjectView <| Py typeError

public instance : ViewPy typeError PyTypeError := ⟨rfl⟩

/-! ### ValueError -/

/--
The Python exception for invalid values, [{lit}`ValueError`][1].

[1]: https://docs.python.org/3/library/exceptions#ValueError
-/
public opaque valueError : Constant

@[inherit_doc valueError, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.valueError : TypeExpr :=
  ⟨"ValueError"⟩

public instance : CoeDep Constant valueError TypeExpr := ⟨.valueError⟩

@[inherit_doc valueError]
public protected def Typing.valueError : Typing :=
  exceptHint valueError
  deriving NonemptyPy

public instance : CoeDep Constant valueError Typing := ⟨.valueError⟩
public instance : ToTypeExpr valueError := ⟨valueError⟩

public instance : PromotableB baseException valueError :=
  ⟨Promotable.infer (U := exceptHint _)⟩

/-- A weakly typed instance of {lit}`ValueError`. -/
public abbrev PyValueError := PyBaseExceptionView <| PyObjectView <| Py valueError

public instance : ViewPy valueError PyValueError := ⟨rfl⟩

/-! ### RuntimeError -/

/--
The type of generic Python errors, [{lit}`RuntimeError`][1].

[1]: https://docs.python.org/3/library/exceptions#RuntimeError
-/
public opaque runtimeError : Constant

@[inherit_doc runtimeError, inline, irreducible, expose] -- for Nerodia compiler reduction
public protected def TypeExpr.runtimeError : TypeExpr :=
  ⟨"RuntimeError"⟩

public instance : CoeDep Constant runtimeError TypeExpr := ⟨.runtimeError⟩

@[inherit_doc runtimeError]
public protected def Typing.runtimeError : Typing :=
  exceptHint runtimeError
  deriving NonemptyPy

public instance : CoeDep Constant runtimeError Typing := ⟨.runtimeError⟩
public instance : ToTypeExpr runtimeError := ⟨runtimeError⟩

public instance : PromotableB baseException runtimeError :=
  ⟨Promotable.infer (U := exceptHint _)⟩

/-- A weakly typed instance of {lit}`RuntimeError`. -/
public abbrev PyRuntimeError := PyBaseExceptionView <| PyObjectView <| Py runtimeError

public instance : ViewPy runtimeError PyRuntimeError := ⟨rfl⟩
