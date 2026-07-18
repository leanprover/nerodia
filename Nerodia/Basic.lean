/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.CPtr
public import Nerodia.Data.Codec
public import Nerodia.Control.MonadPy
public import Nerodia.Control.PyIO.Basic
meta import Nerodia.ViewMethod

/-! # Nerodia -/

namespace Nerodia

/-! ## PyObject -/

/-- A Python type hint. -/
public structure TypeExpr where
  ofString ::
    protected toString : String
    deriving Nonempty, DecidableEq

/-- A fixed enumartion of builtin base types. -/
-- A very simple model, it could be made more dynamic in the future.
inductive Py.Kind
| type
| baseException
| str
| bytes
| module
| other
deriving Nonempty, DecidableEq

/-- The logical model of a Python object. -/
structure Py.Model where
  addr : Addr
  env : PyEnvironment
  hint : TypeExpr
  kind : Py.Kind
  deriving Nonempty

/--
A Python object. A [{lit}`PyObject`][1] pointer managed by Lean.

[1]: https://docs.python.org/3/c-api/structures.html#c.PyObject
-/
public structure Py.Raw where
  private ofModel ::
    private toModel : Py.Model
    deriving Nonempty

/-! ## Type Predicate -/

/-- A Neordia type predicate. -/
@[expose] -- for Lean/Nerodia codegen
public def TypePred : Type :=
  Py.Raw → Prop

namespace TypePred

public def ofFn (p : Py.Raw → Prop) : TypePred :=
  p

public def Mem (T : TypePred) (o : Py.Raw) : Prop :=
  T o

public instance : Membership Py.Raw TypePred := ⟨Mem⟩

@[simp, grind =] public theorem mem_ofFn :
  o ∈ ofFn p ↔ p o
:= Iff.intro id id

@[ext, grind ext] public theorem ext
  {T U : TypePred} (h : ∀ o, o ∈ T ↔ o ∈ U) : T = U
:= funext fun o => propext (h o)

public def union (T : TypePred) (U : TypePred) : TypePred :=
  ofFn fun o => o ∈ T ∨ o ∈ U

public instance : Union TypePred := ⟨union⟩

/--
Constructs the union of two type predicates.
Written as {lean}`T ∪ U`. Equivalent to the Python `T | U`.
-/
add_decl_doc union

@[grind =] public theorem mem_union_iff_or {T U : TypePred} :
  o ∈ T ∪ U ↔ o ∈ T ∨ o ∈ U
:= Iff.intro id id

public theorem Mem.union_left
  {T U : TypePred} (h : o ∈ T) : o ∈ T ∪ U
:= .inl h

public theorem Mem.union_right
  {T U : TypePred} (h : o ∈ U) : o ∈ T ∪ U
:= .inr h

/-- Constructs the union of two type predicates. Equivalent to the Python `T | U`. -/
public def inter (T : TypePred) (U : TypePred) : TypePred :=
  ofFn fun o => o ∈ T ∧ o ∈ U

public instance : Inter TypePred := ⟨inter⟩

/--
Constructs the intersection of two type predicates. Written as {lean}`T ∩ U`.

Python's type system has no equivalent, but [ty][1] represents this
as {lit}`T & U` / {lit}`Intersection[T, U]`.

[1]: https://docs.astral.sh/ty/features/type-system/#intersection-types
-/
add_decl_doc inter

@[grind =] public theorem mem_inter_iff_and {T U : TypePred} :
  o ∈ T ∩ U ↔ o ∈ T ∧ o ∈ U
:= Iff.intro id id

public nonrec theorem Mem.left
  {T U : TypePred} (h : o ∈ T ∩ U) : o ∈ T
:= h.left

public nonrec theorem Mem.right
  {T U : TypePred} (h : o ∈ T ∩ U) : o ∈ U
:= h.right

public def Subset (T : TypePred) (U : TypePred) : Prop :=
  ∀ o, o ∈ T → o ∈ U

public instance : HasSubset TypePred := ⟨Subset⟩

@[grind =] public theorem subset_iff_forall {T U : TypePred} :
  T ⊆ U ↔ ∀ o, o ∈ T → o ∈ U
:= Iff.intro id id

public theorem Subset.mem_of_mem
  {T U : TypePred} (h : T ⊆ U) (ho : o ∈ T)
: o ∈ U := subset_iff_forall.mp h o ho

/-- Python {lit}`object`. The top (⊤) element of type predicates. -/
public def object : TypePred :=
  ofFn fun _ => True

@[simp, grind .] public theorem Mem.object : o ∈ object := True.intro

-- the below are `@[simp]` only because grind already handles them

@[simp] public theorem Subset.object : T ⊆ object :=
  subset_iff_forall.mpr fun _ _ => .object

@[simp] public theorem union_object : T ∪ object = object := by
  simp [TypePred.ext_iff, mem_union_iff_or]

@[simp] public theorem object_union : object ∪ T = object := by
  simp [TypePred.ext_iff, mem_union_iff_or]

@[simp] public theorem inter_object : T ∩ object = T := by
  simp [TypePred.ext_iff, mem_inter_iff_and]

@[simp] public theorem object_inter : object ∩ T = T := by
  simp [TypePred.ext_iff, mem_inter_iff_and]

/-- Python {lit}`Never`. The bottom (⊥) element of type predicates. -/
public def never : TypePred :=
  ofFn fun _ => False

@[simp, grind .] public theorem not_mem_never : ¬ o ∈ never := by
  simp [never]

-- the below are `@[simp]` only because grind already handles them

@[simp] public theorem never_subset : never ⊆ T :=
  subset_iff_forall.mpr fun _ => not_mem_never.elim

@[simp] public theorem union_never : T ∪ never = T := by
  simp [TypePred.ext_iff, mem_union_iff_or]

@[simp] public theorem never_union : never ∪ T = T := by
  simp [TypePred.ext_iff, mem_union_iff_or]

@[simp] public theorem inter_never : T ∩ never = never := by
  simp [TypePred.ext_iff, mem_inter_iff_and]

@[simp] public theorem never_inter : never ∩ T = never := by
  simp [TypePred.ext_iff, mem_inter_iff_and]

end TypePred

/-! ## ToTypeExpr -/

/--
Associates a Python type expression with a Nerodia type predicate.

This class is used by the Nerodia compiler to generate Python type annotations.
For this to work, all instances must be publicly reducible to {lean}`String`.
Thus, definitions they use must be marked {attr}`@[expose]`.
-/
public class ToTypeExpr (T : TypePred) where
  toTypeExpr : TypeExpr

/-! ## Py -/

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

/-! ### IsPy -/

public class inductive IsPy : (α : Type) → Prop
| of_raw : IsPy Py.Raw
| of_py {T} : IsPy (Py T)

public instance : IsPy Py.Raw := .of_raw
public instance : IsPy (Py T) := .of_py

/-! ### NonemptyPy -/

public abbrev NonemptyPy (T : TypePred) := Nonempty (Py T)

public theorem NonemptyPy.intro (o : Py.Raw) (h : o ∈ T) : NonemptyPy T :=
  ⟨⟨o, h⟩⟩

public instance : NonemptyPy .object :=
  .intro Classical.ofNonempty .intro

public instance [NonemptyPy T] : NonemptyPy (T ∪ U) :=
  let o : Py T := Classical.ofNonempty
  .intro o.raw o.raw_mem.union_left

public instance [NonemptyPy U] : NonemptyPy (T ∪ U) :=
  let o : Py U := Classical.ofNonempty
  .intro o.raw o.raw_mem.union_right

/-! ### ToPy -/

public class ToPy (T : TypePred) (α : Type u)  where
  toPy (a : α) : Py T

export ToPy (toPy)

namespace ToPy

public instance : ToPy T (Py T) := ⟨(·)⟩

@[simp, grind =] theorem toPy_eq_self :
  toPy (o : Py T) = o := by rfl

public instance : ToPy T (Py (T ∩ U)) := ⟨Py.left⟩

@[simp, grind =] theorem toPy_eq_left  :
  toPy (o : Py  (T ∩ U)) = o.left := by rfl

public instance : ToPy U (Py (T ∩ U)) := ⟨Py.right⟩

@[simp, grind =] theorem toPy_eq_right :
  toPy (o : Py (T ∩ U)) = o.right := by rfl

public instance [ToPy T Py.Raw] : ToPy T (Py U) := ⟨(toPy ·.raw)⟩

@[simp, grind =] theorem toPy_eq_toPy_raw  [ToPy U Py.Raw] :
  toPy (o : Py T) = toPy (T := U) o.raw := by rfl

end ToPy

/-! ## PyObject -/

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

/-! ## PyAny -/

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

/-! ## Basics -/

namespace Py.Raw

/-- Returns the Python environment to which this object belongs. -/
public noncomputable def env (self : Py.Raw) : PyEnvironment :=
  self.toModel.env

/-- Returns the address of the Python object (not the Lean wrapper). -/
@[extern "nerodia_py_object_addr"]
public def addr (self : @& Py.Raw) : Addr :=
  self.toModel.addr

/--
Returns whether two objects are identical (are the same pointer).

This is equivalent to the Python {lit}`self is other`.
-/
@[extern "nerodia_py_object_dec_eq"]
public def decEq (self other : Py.Raw) : Decidable (self = other) :=
  Classical.propDecidable _

public instance : DecidableEq Py.Raw := decEq

end Py.Raw

/-!
## Weak Typing

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

/--
Casts the object to the type indicating by the expression {lean}`ty`.

This weakly types the object, providing no strong guarantees.

This is akin to the Python {lit}`typing.cast(ty, self)`.
-/
@[implemented_by castImpl]
public def cast (ty : TypeExpr) (self : Py.Raw) : Py.Raw :=
  ⟨{self.toModel with hint := ty}⟩

end Py.Raw

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
## Builtin Types

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

noncomputable def Py.Raw.ofKind (k : Kind) : Py.Raw :=
  {Classical.ofNonempty (α := Py.Raw) with toModel.kind := k}

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

-- /-- An instance of {lit}`BaseException` that is weakly typed as {lit}`ty`. -/
-- public abbrev HPyBaseException (ty : TypeExpr) := TPyBaseException (.hint ty)

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

/-! ## Builtin Type Objects -/

/-- Returns a reference to the type of types (i.e., {lit}`type` in Python). -/
@[extern "nerodia_type_type"]
public opaque PyEnvironment.typeType (env : @& PyEnvironment) : PyType

@[extern "nerodia_type_type", inherit_doc PyEnvironment.typeType]
public abbrev PyContext.typeType (ctx : @& PyContext) : PyType :=
  ctx.env.typeType

/-- Returns a reference to the unicode string type (i.e., {lit}`str` in Python). -/
@[extern "nerodia_str_type"]
public opaque PyEnvironment.strType (env : @& PyEnvironment) : PyType

@[extern "nerodia_str_type", inherit_doc PyEnvironment.strType]
public abbrev PyContext.strType (ctx : @& PyContext) : PyType :=
  ctx.env.strType

/-! ## CPyResult -/

/--
A raw strong reference to a Python object.

**Not memory safe.** The reference's lifetime must be manually managed.
It is not managed by Lean. Nerodia handles this within its API, and users are
not expected to manage {name}`CPyBaseResult` objects manually.
-/
public structure CPyBaseResult (α : Type) extends toCPtrUnsafe : CPtr α where
  /--
  Constructs a {name}`CPyBaseResult` from a raw Python object pointer,
  with both sharing the strong reference.

  **Memory Safety:** Users must ensure the pointer is a strong reference
  and manually manage the reference's lifetime.
  -/
  private ofCPtrUnsafe ::
    [isPy : IsPy α]
    deriving DecidableEq


/--
Converts the {name}`CPyBaseResult` to a raw Pyton object pointer,
with both sharing the strong reference.

**Memory Safety:** Users must manually manage the reference's lifetime.
-/
add_decl_doc CPyBaseResult.toCPtrUnsafe

namespace CPyBaseResult
public instance [IsPy α] [Nonempty α] : Nonempty (CPyBaseResult α) :=
  ⟨⟨Classical.ofNonempty⟩⟩
end CPyBaseResult

/-! ## CPyResult -/

/--
The result of a Python C API function returning a Python object.

Implementation-wise, this is either {lit}`NULL` or a raw strong reference
to a Python object. {lit}`NULL` indicates an exception has been raised.

**Not memory safe.** The result's lifetime must be manually managed.
It is not managed by Lean. Nerodia handles this within its API, and users are
not expected to manage {name}`CPyResult` objects manually.
-/
public structure CPyResult (α : Type) extends toNullableCPtrUnsafe : NullableCPtr α where
  /--
  Constructs a result from a raw Python object pointer
  (or {name}`null`), with both sharing the strong reference.

  **Safety**
  * **Correctness:** Users should ensure that an exception is set if {name}`null`.
  * **Memory:** Users must ensure the pointer is a strong reference
  and manually manage the reference's lifetime.
  -/
  private ofNullableCPtrUnsafe ::
    isPy_of_not_isNull : ¬ toNullableCPtrUnsafe.IsNull → IsPy α
    deriving DecidableEq

namespace CPyResult

/--
Returns the result's raw Python object pointer (or {name}`null`).

**Safety**
* **Correctness:** Users must ensure that the set exception is eventually
handled if {name}`null`.
* **Memory:** Users must manually manage the reference's lifetime.
-/
add_decl_doc toNullableCPtrUnsafe

/--
Constructs a successful {lean}`CPyResult` returning {lean}`o`,
sharing the single strong reference between them.

**Memory Safety:** Users must manually manage the reference's lifetime.
-/
@[inline] def ofCPyBaseResultUnsafe (o : CPyBaseResult α) : CPyResult α :=
  .ofNullableCPtrUnsafe o.toCPtrUnsafe fun _ => o.isPy

/--
Constructs a {lean}`CPyResult` indicating failure.

**Safety:** Users should ensure that an exception is set.
-/
@[inline] public def failureUnsafe : CPyResult α :=
  ⟨null, by simp⟩

public instance : Inhabited (CPyResult α) := ⟨failureUnsafe⟩

abbrev IsFailure (self : CPyResult α) : Prop :=
  self.IsNull

/--
Constructs a {name}`CPyBaseResult` from a successful {name}`CPyResult`,
sharing the single strong reference between them.

**Memory Safety:** Users must manually manage the reference's lifetime.
-/
@[inline] def toCPyBaseResultUnsafe (self : CPyResult α) (h : ¬ self.IsFailure) : CPyBaseResult α :=
  have : IsPy α := self.isPy_of_not_isNull h
  .ofCPtrUnsafe (.ofNullableCPtr self.toNullableCPtrUnsafe h)

/--
Casts a {name}`CPyResult` returning a typed Python object to one returning
its supertype, sharing the single strong reference between them.

**Memory Safety:** Users must manually manage the reference's lifetime.
-/
@[inline] protected def cast (x : CPyResult (Py T)) (h : T ⊆ U) : CPyResult (Py U) :=
  let cptr := .ofNullableAddrUnsafe x.toNullableCPtrUnsafe.nullableAddr fun h' =>
    let t := Classical.choice <| x.toNullableCPtrUnsafe.nonempty_of_not_isNull h'
    ⟨Py.mk t.raw (h.mem_of_mem t.raw_mem)⟩
  .ofNullableCPtrUnsafe cptr fun _ => inferInstance

/--
Casts a {name}`CPyResult` returning anything to one returning
an untyped object, sharing the single strong reference between them.

**Memory Safety:** Users must manually manage the reference's lifetime.
-/
@[inline] def raw (x : CPyResult α) : CPyResult Py.Raw :=
  let cptr := .ofNullableAddrUnsafe x.toNullableCPtrUnsafe.nullableAddr fun h' =>
    let a := Classical.choice <| x.toNullableCPtrUnsafe.nonempty_of_not_isNull h'
    match x.isPy_of_not_isNull h', a with
    | .of_raw, a => ⟨a⟩
    | .of_py, a => ⟨a.raw⟩
  .ofNullableCPtrUnsafe cptr fun _ => inferInstance

end CPyResult

/-! ## C Monad Types -/

/--
Return context for external CPython functions that return an object
and may raise an exception.

Not a monad itself, but lifts into monads equipped with a Python context.
-/
@[expose] -- for codegen
public def CPyIO (α) :=
  BaseIO (CPyResult α)


namespace CPyIO

/-- Constructs a {lean}`CPyIO` function from its definition.  -/
@[inline] def ofBaseIOUnsafe (x : BaseIO (CPyResult α)) : CPyIO α :=
  x

/--
Runs the {lean}`CPyIO` function, returning the raw, unmanaged pointer.

**Safety**
* Users must ensure a Python context exists.
* Users must ensure the raised exception is handled on {name}`CPyResult.IsFailure`.
* **Memory:** Users must ensure that a returned object reference is consumed,
and that it does not outlive the enviroment.
-/
@[inline] def toBaseIOUnsafe (x : CPyIO α) : BaseIO (CPyResult α) :=
  x

/--
Constructs a {lean}`CPyIO` that fails.

**Safety:** Users should ensure that an exception is set.
-/
@[inline] def failureUnsafe : CPyIO α :=
  ofBaseIOUnsafe <| pure .failureUnsafe

public instance : Nonempty (CPyIO α) := ⟨failureUnsafe⟩

/-- Constructs a {lean}`CPyIO` using the result of {lean}`x`. -/
@[inline] public def ofBind (x : BaseIO α) (f : α → CPyIO β) : CPyIO β :=
  ofBaseIOUnsafe do f (← x)

set_option linter.unusedVariables.funArgs false in
/--
Converts a {lean}`CPyIO` returning a
typed Python object to one returning its supertype.
-/
@[inline] public def cast (x : CPyIO (Py T)) (h : T ⊆ U) : CPyIO (Py U) :=
  x.map (·.cast h)

/--
Converts a {lean}`CPyIO` returning a
arbitrary type to one returning {lean}`Py.Raw`.
-/
@[inline] public def raw (x : CPyIO α) : CPyIO Py.Raw :=
  x.map (·.raw)

public instance : CoeOut (CPyIO (Py T)) (CPyIO Py.Raw) := ⟨CPyIO.raw⟩

end CPyIO

/--
Return context for external CPython functions that return an object
and cannot raise an exception.

Not a monad itself, but lifts into monads equipped with a Python context.
-/
@[expose] -- for codegen
public def CPyBaseIO (α) :=
  BaseIO (CPyBaseResult α)

namespace CPyBaseIO

@[inline] def ofBaseIOUnsafe (x : BaseIO (CPyBaseResult α)) : CPyBaseIO α :=
  x

/--
Runs the {lean}`CPyBaseIO` function, returning the raw, unmanaged pointer.

**Safety**
* Users must ensure a Python context exists.
* **Memory:** Users must ensure that the returned object reference is consumed,
and that it  does not outlive the enviroment.
-/
@[inline] def toBaseIOUnsafe (x : CPyBaseIO α) : BaseIO (CPyBaseResult α) :=
  x

/-- Constructs a {lean}`CPyBaseIO` using the result of {lean}`x`. -/
@[inline] public def ofBind (x : BaseIO α) (f : α → CPyBaseIO β) : CPyBaseIO β :=
  ofBaseIOUnsafe do f (← x)

/-- Lifts a {lean}`CPyBaseIO` into a successful {lean}`CPyIO`. -/
@[inline] public def toCPyIO (x : CPyBaseIO α) : CPyIO α :=
  .ofBaseIOUnsafe <| x.toBaseIOUnsafe.map CPyResult.ofCPyBaseResultUnsafe

public instance : MonadLift CPyBaseIO CPyIO := ⟨CPyBaseIO.toCPyIO⟩

end CPyBaseIO

/--
Wraps a strong Python object reference into a memory-managed Lean object,
stealing the reference.

**Memory Safety:** {lean}`o` is now borrowed, so its reference must not be
consumed and uses must not outlive the returned Lean object.
-/
-- the resulting object keeps `env` alive
@[extern "nerodia_mk_object"]
opaque PyEnvironment.mkObjectUnsafe (env : @& PyEnvironment) (o : CPyBaseResult α) : α :=
  Classical.choice o.nonempty

@[extern "nerodia_mk_object", inherit_doc PyEnvironment.mkObjectUnsafe]
abbrev PyContext.mkObjectUnsafe (ctx : @& PyContext) (o : CPyBaseResult α) : α :=
  Classical.choice o.nonempty

@[inline, inherit_doc PyEnvironment.mkObjectUnsafe]
public def ofBaseResultUnsafe
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m]
  (r : CPyBaseResult α)
: m α := return (← getPyContextUnsafe).mkObjectUnsafe r

namespace CPyBaseIO

/-- Lifts a {lean}`CPyBaseIO` into {lean}`PyBaseIO`. -/
@[inline] public def toPyBaseIO (x : CPyBaseIO α) : PyBaseIO α := do
  ofBaseResultUnsafe (← x.toBaseIOUnsafe)

public instance : MonadLift CPyBaseIO PyBaseIO := ⟨toPyBaseIO⟩

end CPyBaseIO

/--
Runs {lean}`e` if {lean}`x` has set an exception.

**Safety:** {lean}`e` must handle the set exception (i.e., at least clear it).
-/
@[inline] public def CPyIO.tryCatchUnsafe
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m]
  (x : CPyIO α) (e : m α)
: m α := do
  let res ← x.toBaseIOUnsafe
  if h : res.IsFailure then
    -- Other branch ensure context is held until here
    e
  else
    ofBaseResultUnsafe (res.toCPyBaseResultUnsafe h)

/-- Returns a new strong reference to Python object's raw unmanaged C pointer. -/
@[extern "nerodia_py_object_new_ref"]
def Py.newRef (self : @& Py T) : CPyBaseIO (Py T) :=
  have : Nonempty (Py T) := ⟨self⟩
  let cptr := .ofAddrUnsafe self.raw.addr
  .ofBaseIOUnsafe <| pure (.ofCPtrUnsafe cptr)

namespace CPyBaseIO

/-- Constructs a {lean}`CPyBaseIO` that returns {lean}`o`. -/
@[inline] public protected def pure (o : Py T) : CPyBaseIO (Py T) :=
  o.newRef

public instance [IsPy α] [Nonempty α] : Nonempty (CPyBaseIO α) :=
  ⟨ofBaseIOUnsafe <| pure <| Classical.ofNonempty⟩

end CPyBaseIO

/-- Constructs a successful {lean}`CPyIO` that returns {lean}`o`. -/
@[inline] public protected abbrev CPyIO.pure (o : Py T) : CPyIO (Py T) :=
  CPyBaseIO.pure o |>.toCPyIO

/--
Sequences a {lean}`CPyBaseIO` action after a {lean}`PyBaseIO` action.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyBaseIO.bindCPyBaseIO
  (x : PyBaseIO α) (f : α → CPyBaseIO β)
: CPyBaseIO β := .ofBaseIOUnsafe do
  let ctx ← PyContext.getOrInit
  f (← x.runUnsafe ctx)

/--
Runs a {lean}`PyBaseIO` action producing a Python object in {lean}`CPyBaseIO`.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyBaseIO.toCPyBaseIO (x : PyBaseIO (Py T)) : CPyBaseIO (Py T) :=
  x.bindCPyBaseIO CPyBaseIO.pure

/--
Sequences a {lean}`CPyIO` action after a {lean}`PyBaseIO` action.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyBaseIO.bindCPyIO
  (x : PyBaseIO α) (f : α → CPyIO β)
: CPyIO β := .ofBaseIOUnsafe do
  let ctx ← PyContext.getOrInit
  f (← x.runUnsafe ctx)

/--
Sequences a {lean}`CPyIO` action after a {lean}`PyIO` action.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyIO.bindCPyIO (x : PyIO α) (f : α → CPyIO β) : CPyIO β := .ofBaseIOUnsafe do
  let ctx ← PyContext.getOrInit
  match (← x.runUnsafe? ctx) with
  | some a => f a
  | none => CPyIO.failureUnsafe

/--
Runs a {lean}`PyIO` action producing a Python object in {lean}`CPyIO`.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyIO.toCPyIO (x : PyIO (Py T)) : CPyIO (Py T) :=
  x.bindCPyIO CPyIO.pure

/--
Return type for external CPython functions that may error but do not return
a Python object.

Not a monad itself, but lifts into monads equipped with a Python context.
-/
@[expose] -- for codegen
public def CPyUnitIO :=
  BaseIO Int32

namespace CPyUnitIO

/--
Constructs a {lean}`CPyUnitIO` function from its definition.

**Safety:** Users should esnure that an exception is set on error.
-/
@[inline] def mkUnsafe (x : BaseIO Int32) : CPyUnitIO :=
  x

/--
Runs the {lean}`CPyUnitIO` function.

**Safety:** Users must ensure that a set exception is handled.
-/
@[inline] def runUnsafe (x : CPyUnitIO) : BaseIO Int32 :=
  x

/-- Constructs a {lean}`CPyUnitIO` that succeeds. -/
@[inline] public def ok : CPyUnitIO :=
  mkUnsafe <| pure 0

public instance : Nonempty CPyUnitIO := ⟨ok⟩

/--
Constructs a {lean}`CPyUnitIO` that fails.

**Safety:** Users should ensure that an exception is set.
-/
@[inline] def failureUnsafe : CPyUnitIO :=
  mkUnsafe <| pure (-1)

end CPyUnitIO

/--
Runs a {lean}`PyIO` action producing nothing in {lean}`CPyUnitIO`.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyIO.toCPyUnitIO (x : PyIO Unit) : CPyUnitIO := .mkUnsafe do
  let ctx ← PyContext.getOrInit
  match ( ← x.runUnsafe? ctx) with
  | some _ => CPyUnitIO.ok
  | none => CPyUnitIO.failureUnsafe

/-! ## Exception Handling -/

/-- Type class for monads that can raise Python exceptions. -/
public class MonadRaise (m : Type u → Type v) where
   /-- Raises the exception {lean}`e`.-/
  raise (e : PyBaseException) : m α

 /-- Raises the exception {lean}`e`.-/
@[inline] public def raise [MonadRaise m] [ToPyBaseException ε] (e : ε) : m α :=
  MonadRaise.raise (toPy e)

/-- Clears the current exception. Does nothing if there is none. -/
@[extern "nerodia_py_context_clear_error"]
public opaque PyContext.clearError (ctx : @& PyContext) : BaseIO Unit

@[inline, inherit_doc PyContext.clearError]
public def clearError [Bind m] [MonadPy m] [MonadLiftT BaseIO m] : m PUnit :=
  getPyContextUnsafe >>= (·.clearError)

/--
Constructs a {lit}`SystemError` with the string {lean}`msg`.
Panics if the construction fails (e.g., due to lack of memeory).
-/
@[extern "nerodia_py_context_system_error"]
opaque PyContext.systemError! (msg : @& String) (ctx : @& PyContext) : PySystemError

/-- The exception used when when no other exception is set. -/
@[inline] public opaque PyContext.unsetException (ctx : PyContext) : PySystemError :=
  ctx.systemError! "no exception was set"

@[inline, inherit_doc PyContext.unsetException]
def getUnsetException  [Functor m] [MonadPy m] : m PyBaseException :=
  (·.unsetException) <$> getPyContextUnsafe

/-- Clears the current exception and returns it. -/
@[extern "nerodia_get_raised_exception"]
opaque getCRaisedException : CPyIO PyBaseException

/--
Clears the current exception and returns it.
If none, instead returns {name}`PyContext.unsetException`.
-/
@[inline] public def getRaisedException
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m]
: m PyBaseException := getCRaisedException.tryCatchUnsafe getUnsetException

/-- Returns the currently raised exception or {name}`unsetException` if none. -/
@[inline] protected def PyContext.getRaisedException (ctx : PyContext) : BaseIO PyBaseException :=
  PyBaseIO.runUnsafe ctx getRaisedException

/--
Sets the currently raised exception to {lean}`e`.

**Safety:** Users must ensure the exception is handled or signaled.
-/
@[extern "nerodia_set_raised_exception"]
opaque setRaisedExceptionUnsafe (e : @& PyBaseException) : BaseIO Unit

namespace PyIO

/--
Runs the {lean}`PyIO` function in {lean}`EIO`.

This creates a new temporary Python context for the call.
As such, it should only be used when another Python context is not available.
Otherwise, lift {lean}`x` into a supporting monad.
-/
@[inline] public def toEIO (x : PyIO α) : EIO PyBaseException α := do
  let ctx ← PyContext.getOrInit
  (← x.runUnsafe? ctx).getDM do
    throw (← ctx.getRaisedException)

/-- Raises the exception {lean}`e`. -/
@[inline] public protected def raise (e : PyBaseException) : PyIO α := do
  setRaisedExceptionUnsafe e
  PyIO.failureUnsafe

public instance : MonadRaise PyIO := ⟨PyIO.raise⟩

/--
Runs the {name}`PyIO` action {name}`x`.
If {name}`x` raises an exception {given}`e`, catches it and runs {lean}`f e`.
Exceptions in {name}`f` are not caught.
-/
@[inline] public protected def tryCatch
  [Monad m] [MonadLiftT BaseIO m] [MonadPy m]
  (x : PyIO α) (f : PyBaseException → m α)
: m α := do
  let ctx ← getPyContextUnsafe
  (← x.runUnsafe? ctx).getDM do
    f (← ctx.getRaisedException)

public instance : MonadExceptOf PyBaseException PyIO where
  throw := PyIO.raise
  tryCatch := PyIO.tryCatch

/--
Runs the {name}`PyIO` action {name}`x`,
encursing some other action always happens afterwards.

If {name}`x` raises an exception, catches it, runs {lean}`f none`, and then
re-reaises the exception. Otherwise, if {name}`x` succeeds and returns
{given}`a : α`, runs {lean}`f (some a)`.
-/
@[inline] public protected def tryFinally'
  [Monad m] [MonadLiftT BaseIO m] [MonadPy m] [MonadRaise m]
  (x : PyIO α) (f : Option α → m β)
: m (α × β) := do
  let ctx ← getPyContextUnsafe
  if let some a ← x.runUnsafe? ctx then
    let b ← f (some a)
    return (a, b)
  else
    -- TODO: Should this set `e` as the handled exception for Python?
    let e ← getRaisedException
    let _ ← f none
    raise e

public instance : MonadFinally PyIO := ⟨PyIO.tryFinally'⟩

/--
Runs the {name}`PyIO` action {name}`x`.
If {name}`x` raises an exception, clears it and runs {lean}`f ()`.
-/
@[inline] public protected def orElse
  [Monad m] [MonadLiftT BaseIO m] [MonadPy m]
  (x : PyIO α) (f : Unit → m α)
: m α := do
  let ctx ← getPyContextUnsafe
  if let some a ← x.runUnsafe? ctx then
    return a
  else
    ctx.clearError
    f ()

public instance : OrElse (PyIO α) := ⟨PyIO.orElse⟩

end PyIO

namespace CPyIO

/--
Runs the {lean}`CPyIO` function in a supporting monad.
If a Python error occurs, it is raised via {name}`throw`.
-/
@[inline] public def run
  [Monad m] [MonadPy m]
  [MonadExcept PyBaseException m] [MonadLiftT BaseIO m]
  (x : CPyIO α)
: m α := x.tryCatchUnsafe do throw (← getRaisedException)

/--
Runs the {lean}`CPyIO` function in a supporting monad
If a Python error occurs, it is set as the exception.
-/
public abbrev toExceptT
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m] (x : CPyIO α)
: ExceptT PyBaseException m α := x.run

/-- Lifts the {lean}`CPyIO` function into {lean}`PyIO`, reusing its Python context. -/
@[inline] public def toPyIO (x : CPyIO α) : PyIO α :=
  x.tryCatchUnsafe .failureUnsafe

public instance : MonadLift CPyIO PyIO := ⟨toPyIO⟩

/--
Runs the {lean}`CPyIO` function in {lean}`EIO`.

This creates a new temporary Python context for the call.
As such, it should only be used when a Python context is not available.
Otherwise, run {lean}`x` via {name}`run` or lift it into {lean}`PyIO`
(via {lean}`toPyIO`) and run it from there.
-/
@[inline] public def toEIO (x : CPyIO α) : EIO PyBaseException α :=
  x.toPyIO.toEIO

/--
Runs the {lean}`CPyIO` function in a supporting monad.
If a Python error occurs, it is cleared and {name}`failure` is called.
-/
@[inline] public def run'
  [Monad m] [MonadPy m]
  [Alternative m] [MonadLiftT BaseIO m]
  (x : CPyIO α)
: m α := x.tryCatchUnsafe do
  (← getPyContextUnsafe).clearError
  failure

/--
Runs the {lean}`CPyIO` function in a supporting monad
If a Python error occurs, it is cleared and {lean}`none` is set.
-/
public abbrev toOptionT
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m] (x : CPyIO α)
: OptionT m α := x.run'

/--
Runs the {lean}`CPyIO` function in a supporting monad.
If a Python error occurs, it is cleared and {lean}`none` is returned.
-/
public abbrev run?
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m] (x : CPyIO α)
: m (Option α) := x.toOptionT.run

/-- Raises the exception {lean}`e`.  -/
@[inline] public protected def raise (e : PyBaseException) : CPyIO α := .ofBaseIOUnsafe do
  setRaisedExceptionUnsafe e
  CPyIO.failureUnsafe

public instance : MonadRaise CPyIO := ⟨CPyIO.raise⟩

@[inline] public protected def tryCatch
  [Monad m] [MonadLiftT BaseIO m] [MonadPy m]
  (x : CPyIO α) (f : PyBaseException → m α)
: m α := x.tryCatchUnsafe do f (← getRaisedException)

end CPyIO

namespace CPyUnitIO

/--
Runs the {lean}`CPyIO` function in a supporting monad.
If a Python error occurs, it is raised via {name}`throw`.
-/
@[inline] public def run
  [Monad m] [MonadPy m]
  [MonadExcept PyBaseException m] [MonadLiftT BaseIO m]
  (x : CPyUnitIO)
: m PUnit := do
  let ctx ← getPyContextUnsafe
  if (← x.runUnsafe) < 0 then
    throw (← ctx.getRaisedException)

/--
Runs the {lean}`CPyUnitIO` function in a supporting monad
If a Python error occurs, it is set as the exception.
-/
public abbrev toExceptT
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m] (x : CPyUnitIO)
: ExceptT PyBaseException m PUnit := x.run

/--
Lifts the {lean}`CPyUnitIO` function into {lean}`PyIO`,
reusing its Python context.
-/
@[inline] public def toPyIO (x : CPyUnitIO) : PyIO Unit := do
  if (← x.runUnsafe) < 0 then
    .failureUnsafe

public instance : Coe CPyUnitIO (PyIO Unit) := ⟨toPyIO⟩

/--
Runs the {lean}`CPyUnitIO` function in {lean}`EIO`.

This creates a new temporary Python context for the call.
As such, it should only be used when a Python context is not available.
Otherwise, run {lean}`x` via {name}`run` or lift it into {lean}`PyIO`
(via {lean}`toPyIO`) and run it from there.
-/
@[inline] public def toEIO (x : CPyUnitIO) : EIO PyBaseException Unit :=
  x.toPyIO.toEIO

/--
Runs the {lean}`CPyUnitIO` function in a supporting monad.
If a Python error occurs, it is cleared and {name}`failure` is called.
-/
@[inline] public def run'
  [Monad m] [MonadPy m]
  [Alternative m] [MonadLiftT BaseIO m]
  (x : CPyUnitIO)
: m PUnit := do
  let ctx ← getPyContextUnsafe
  if (← x.runUnsafe) < 0 then
    ctx.clearError
    failure

end CPyUnitIO

/-! ## PyResultIO -/

@[expose] -- for codegen
public def PyResultIO (α : Type) := PyBaseIO (CPyResult α)

namespace PyResultIO

@[inline] def ofPyBaseIOUnsafe (x : PyBaseIO (CPyResult α)) : PyResultIO α :=
  x

@[inline] def toPyBaseIOUnsafe (x : PyResultIO α) : PyBaseIO (CPyResult α) :=
  x

@[inline] def runUnsafe (ctx : PyContext) (x : PyResultIO α) : BaseIO (CPyResult α) :=
  x.toPyBaseIOUnsafe.runUnsafe ctx

/-- Constructs a {lean}`PyResultIO` that returns {lean}`o`. -/
@[inline] public protected def pure (o : Py T) : PyResultIO (Py T) :=
  .ofPyBaseIOUnsafe <| .ofBaseIO do
    -- `newRef` does not require an attached thread state,
    -- so we do not need to keep hold of the context (via `Runetime.hold`)
    return .ofCPyBaseResultUnsafe (← o.newRef.toBaseIOUnsafe)

/--
Runs a {lean}`PyResultIO` action producing a Python object in {lean}`CPyIO`.

This creates a new temporary Python context for the call.
-/
@[inline] public def toCPyIO (x : PyResultIO α) : CPyIO α := .ofBaseIOUnsafe do
  x.runUnsafe (← PyContext.getOrInit)

/--
Converts a {lean}`PyResultIO` returning a
arbitrary type to one returning {lean}`Py.Raw`.
-/
@[inline] public def raw (x : PyResultIO α) : PyResultIO Py.Raw :=
  .ofPyBaseIOUnsafe do return (← x.toPyBaseIOUnsafe).raw

end PyResultIO

@[inline] public def CPyIO.toPyResultIO (x : CPyIO α) : PyResultIO α := .mk fun ctx => do
  let r ← x.toBaseIOUnsafe
  Runtime.hold ctx
  return r

/-- Sequences a {lean}`PyResultIO` action after a {lean}`PyBaseIO` action. -/
@[inline] public def PyBaseIO.bindPyResultIO
  (x : PyBaseIO α) (f : α → PyResultIO β)
: PyResultIO β := .mk fun ctx => do
  f (← x.runUnsafe ctx) |>.runUnsafe ctx

/-- Sequences a {lean}`PyResultIO` action after a {lean}`PyIO` action. -/
@[inline] public def PyIO.bindPyResultIO
  (x : PyIO α) (f : α → PyResultIO β)
: PyResultIO β := .mk fun ctx => do
  match (← x.runUnsafe? ctx) with
  | some a => f a |>.runUnsafe ctx
  | none => pure .failureUnsafe

/-- Internal function for {lit}`@[py_module_fn]` -/
@[inline] public def Internal.pyBind
  {α : Type} (x : PyIO α) (f : α → PyResultIO Py.Raw)
: PyResultIO Py.Raw := x.bindPyResultIO f

/-! ## CPyArg -/

/--
A raw Python function argument (a borrowed Python object reference).

**Not memory safe.** The reference must not escape the function.
This is not managed by Lean. Nerodia handles this within its API, and users are
not expected to manage {name}`CPyArg` objects manually.
-/
public structure CPyArg (T : TypePred := .object) where
  private ofCPtrUnsafe ::
    private toCPtrUnsafe : CPtr (Py T)

/--
Wraps a borrowed Python object reference into a memory-managed Lean object.

**Memory Safety:** Users must ensure the reference currently valid
(e.g., it has not escaped its original function).
-/
@[extern "nerodia_py_context_mk_arg"]
def PyContext.mkArgUnsafe (ctx : @& PyContext) (arg : CPyArg T) : (Py T) :=
  Classical.choice arg.toCPtrUnsafe.nonempty

/--
A raw C pointer array of Python function arguments
(borrowed Python object references).

**Not memory safe.** The references must not escape the function.
This is not managed by Lean. Nerodia handles this within its API, and users are
not expected to manage {name}`CPyArgs` objects manually.
 -/
public structure CPyArgs where
  private ofAddrUnsafe ::
    private addr : Addr

@[extern "nerodia_py_context_mk_args"]
opaque PyContext.mkArgsUnsafe
  (ctx : @& PyContext) (args : CPyArgs) (nargs : USize) : Array PyObject

@[extern "nerodia_py_context_mk_nth_arg"]
opaque PyContext.mkNthArgUnsafe
  (ctx : @& PyContext) (args : CPyArgs) (i : USize) : PyObject

/-! ## Python Methods -/

@[extern "nerodia_set_py_type_error"]
opaque setPyTypeErrorUnsafe (msg : @& String) : BaseIO Unit

/-- Raises a {lean}`PyTypeError` with the given message {lean}`msg`. -/
@[inline] public def raisePyTypeError (msg : String) : CPyIO α := .ofBaseIOUnsafe do
  setPyTypeErrorUnsafe msg
  return .failureUnsafe

/-- Raises a {lean}`PyTypeError` indicating {lit}`fn` was called with the wrong number of arguments. -/
@[inline] def raiseArityNotEq (fn : String) (expected given : USize) : CPyIO α :=
  raisePyTypeError s!"{fn} takes exactly {expected} arguments ({given} given)"

/-- The type of a Python method with no arguments. -/
@[expose] -- for codegen
public def PyMethNoArgs :=
  (self : CPyArg) → Null → CPyIO Py.Raw

@[inline] public def PyMethNoArgs.ofPyIO
  (x : (self : PyObject) → PyIO PyAny)
: PyMethNoArgs := fun self _ => PyIO.toCPyIO do
  let ctx ← getPyContextUnsafe
  let self := ctx.mkArgUnsafe self
  x self

@[inline] public def PyMethNoArgs.ofPyIO'
  (x : PyIO PyAny)
: PyMethNoArgs := ofPyIO fun _ => x

@[inline] public def PyMethNoArgs.ofCPyIO
  [IsPy α] (x : CPyIO α)
: PyMethNoArgs := fun _ _ => x.raw

/-- Internal function for {lit}`@[py_module_fn]`. -/
@[inline] public def Internal.mkPyMethNoArgs
  (x : CPyIO Py.Raw)
: PyMethNoArgs := PyMethNoArgs.ofCPyIO x

/-- The type of a Python method with a single positional argument. -/
@[expose] -- for codegen
public def PyMethFastCall :=
  (self : CPyArg) → (args : CPyArgs) → (nargs : USize) → CPyIO Py.Raw

@[inline] public def PyMethFastCall.ofPyIO
  (x : (self : PyObject) → (args : Array PyObject) → PyIO (Py T))
: PyMethFastCall := fun self args nargs => PyIO.toCPyIO do
  let ctx ← getPyContextUnsafe
  let self := ctx.mkArgUnsafe self
  let args := ctx.mkArgsUnsafe args nargs
  x self args

/-- Internal function for {lit}`@[py_module_fn]`. -/
@[inline] public def Internal.mkPyMethFastCallUnsafe
  (fn : String) (arity : USize)
  (x : (args : CPyArgs) → PyResultIO Py.Raw)
: PyMethFastCall := fun _ args nargs =>
  if nargs = arity then
    x args |>.toCPyIO.raw
  else
    raiseArityNotEq fn arity nargs

/-- The type of a Python method with a single positional argument. -/
@[expose] -- for codegen
public def PyMethO :=
  (self : CPyArg) → (arg : CPyArg) → CPyIO Py.Raw

@[inline] public def PyMethO.ofPyIO
  (x : (self : PyObject) → (arg : PyObject) → PyIO (Py T))
: PyMethO := fun self arg => PyIO.toCPyIO do
  let ctx ← getPyContextUnsafe
  let self := ctx.mkArgUnsafe self
  let arg := ctx.mkArgUnsafe arg
  x self arg

@[inline] public def PyMethO.ofPyIO'
  (x : (arg : PyObject) → PyIO (Py T))
: PyMethO := ofPyIO fun _ => x

/-- Internal function for {lit}`@[py_module_fn]`. -/
@[inline] public def Internal.mkPyMethO
  (x : (arg : PyObject) → PyResultIO Py.Raw)
: PyMethO := fun _ arg => PyResultIO.toCPyIO <| .ofPyBaseIOUnsafe do
  let ctx ← getPyContextUnsafe
  let arg := ctx.mkArgUnsafe arg
  x arg |>.toPyBaseIOUnsafe

/-- The type of a Python module initialization function. -/
@[expose] -- for codegen
public def PyModuleInit :=
  (mod : CPyArg .module) → CPyUnitIO

@[inline] public def PyModuleInit.ofPyIO
  (x : PyModule → PyIO Unit)
: PyModuleInit := fun mod => PyIO.toCPyUnitIO do
  let ctx ← getPyContextUnsafe
  x (ctx.mkArgUnsafe mod)

public instance : Inhabited PyModuleInit := ⟨.ofPyIO fun _ _ => return⟩

/-! ## PyType -/

namespace PyType

/-- Returns the qualified name of the type. -/
@[extern "nerodia_py_type_get_qual_name"]
public opaque getQualName (self : @& PyType) : CPyIO PyStr

@[extern "nerodia_py_type_is_heap_type"]
public opaque isHeapType (self : @& PyType) : Bool

@[extern "nerodia_py_type_is_immutable"]
public opaque isImmutable (self : @& PyType) : Bool

end PyType

/-! ## Type -/

/--
Returns the type of the object {lean}`self`.

This is equivalent to {lit}`type(self)` in Python.
-/
@[extern "nerodia_py_object_get_type", view_method]
public opaque PyObject.getType (self : @& PyObject) : CPyBaseIO PyType

/-! ## Module -/

/--
Imports the module named {lean}`modName`.

In Python, the import can be anything, so this may not return a {lean}`PyModule`.
-/
@[extern "nerodia_import"]
public opaque «import» (modName : @& String) : CPyIO PyAny

namespace PyModule

/-- Adds an object {lean}`val` to the module {lean}`self` as {lean}`name`. -/
@[extern "nerodia_py_module_add_by_string"]
public opaque addByString (name : @& String) (val : @& PyObject) (self : @& PyModule) : CPyUnitIO

end PyModule

/-! ## None -/

@[inline, expose] public def TypeExpr.none : TypeExpr :=
  ⟨"None"⟩

noncomputable opaque PyEnvironment.noneAddr (env : PyEnvironment) : Addr

noncomputable def PyEnvironment.noneRaw (env : @& PyEnvironment) : Py.Raw :=
  .ofModel {env, addr := env.noneAddr, hint := .none, kind := .other}

public def TypePred.none : TypePred :=
  ofFn fun o => o = o.env.noneRaw

theorem PyEnvironment.noneRaw_mem_none {env} : noneRaw env ∈ TypePred.none := by
  simp [PyEnvironment.noneRaw, Py.Raw.env, TypePred.none]

public instance : ToTypeExpr .none := ⟨.none⟩

open PyEnvironment in
public instance : NonemptyPy .none :=
  .intro (noneRaw Classical.ofNonempty) noneRaw_mem_none

/-- A Python {lit}`None` constant. -/
public abbrev PyNone := PyObjectView (Py .none)

open Classical in
/-- Equivalent to the Python {lit}`self is None`. -/
@[extern "nerodia_py_object_is_none", view_method]
public def PyObject.isNone (self : PyObject) : Bool :=
  @decide (self.raw ∈ TypePred.none) (Classical.propDecidable _)

@[grind _=_]
public theorem PyObject.isNone_iff_mem : isNone o ↔ o.raw ∈ TypePred.none := by
  simp [PyObject.isNone]

@[simp] public theorem PyNone.isNone_eq_true : (o : PyNone).isNone = true := by
  simp [PyObject.isNone_iff_mem]

/-- Returns a reference to the {lit}`None` constant. -/
@[extern "nerodia_none"]
public def PyEnvironment.none (env : @& PyEnvironment) : PyNone :=
  ⟨env.noneRaw, noneRaw_mem_none⟩

@[extern "nerodia_none", inherit_doc PyEnvironment.none]
public abbrev PyContext.none (ctx : @& PyContext) : PyNone :=
  ctx.env.none

/-- Returns the {lit}`None` constant of the Python environment. -/
@[inline] public def getPyNone [Functor m] [MonadPyEnv m] : m PyNone :=
  (·.none) <$> getPyEnvironment

/-- Returns the {lit}`None` constant of the Python environment. -/
@[inline] public def getCPyNone : CPyBaseIO PyNone :=
  PyBaseIO.toCPyBaseIO getPyNone

/-! ## Compiler Helper Type Classes -/

/--
Type class used to construct a Lean object from a Python function argument.

Used by {lit}`@[py_module_fn]`.
-/
public class OfPyArg (α : Type) (T : outParam TypePred) where
  ofPyArg (fn : String) (i : Nat) : PyObject → PyIO α

/-- **Do not use.** Internal function for {lit}`@[py_module_fn]`.  -/
@[inline] public def Internal.ofPyArgUnsafe
  [OfPyArg α T] (fn : String) (i : USize) (args : CPyArgs)
: PyIO α := do
  let obj := ((← getPyContextUnsafe).mkNthArgUnsafe args i)
  OfPyArg.ofPyArg fn (i.toNat+1) obj

/--
Type class used to construct Python return values from Lean objects.

Used by {lit}`@[py_module_fn]` and {lit}`@[py_module_attr]`.
-/
public class MkCResult (α : Type u) (T : outParam TypePred) where
  mkCResult : α → CPyIO (Py T)

/-- Internal function for {lit}`@[py_module_fn]` and {lit}`@[py_module_attr]` -/
@[inline] public def Internal.mkCResult {α} {T} [MkCResult α T] (a : α) : CPyIO Py.Raw :=
  MkCResult.mkCResult a |>.raw

public instance : MkCResult PUnit .none where
  mkCResult _ := getCPyNone

public instance : MkCResult (Py T) T where
  mkCResult o := CPyBaseIO.pure o

public instance [MkCResult α T] : MkCResult (BaseIO α) T where
  mkCResult x := .ofBind x MkCResult.mkCResult

public instance [MkCResult α T] : MkCResult (PyBaseIO α) T where
  mkCResult x := x.bindCPyIO MkCResult.mkCResult

public instance [MkCResult α T] : MkCResult (PyIO α) T where
  mkCResult x := x.bindCPyIO MkCResult.mkCResult

/--
Type class used to construct Python return values from Lean objects.

Used by {lit}`@[py_module_fn]`.
-/
public class MkResult (α : Type u) (T : outParam TypePred) where
  mkResult : α → PyResultIO (Py T)

/-- Internal function for {lit}`@[py_module_fn]` -/
@[inline] public def Internal.mkResult {α} {T} [MkResult α T] (a : α) : PyResultIO Py.Raw :=
  MkResult.mkResult a |>.raw

public instance (priority := low) [MkCResult α T] : MkResult α T where
  mkResult x := CPyIO.toPyResultIO (MkCResult.mkCResult x)

public instance (priority := low) [MkResult α T] : MkCResult α T where
  mkCResult x := PyResultIO.toCPyIO (MkResult.mkResult x)

public instance : MkResult (Py T) T where
  mkResult o := PyResultIO.pure o

public instance [MkResult α T] : MkResult (BaseIO α) T where
  mkResult x := PyBaseIO.bindPyResultIO x MkResult.mkResult

public instance [MkResult α T] : MkResult (PyBaseIO α) T where
  mkResult x := x.bindPyResultIO MkResult.mkResult

public instance [MkResult α T] : MkResult (PyIO α) T where
  mkResult x := x.bindPyResultIO MkResult.mkResult

@[expose] -- for codegen
public def PyAttrInit :=
  CPyIO Py.Raw

@[inline] public def PyAttrInit.ofCPyIO (x : CPyIO α) : PyAttrInit :=
  x.raw

/-- Internal function for {lit}`@[py_module_attr]` -/
@[inline] public def Internal.mkPyAttrInit (x : CPyIO Py.Raw) : PyAttrInit :=
  PyAttrInit.ofCPyIO x

/-! ## Attributes -/

/-- Returns the attribute named {lean}`attrName` on {lean}`self`. -/
@[extern "nerodia_py_object_get_attr_by_string", view_method]
public opaque PyAny.getAttrByString
  (self : @& PyAny) (attrName : @& String) : CPyIO PyAny

/-! ## Strings & ByteArray -/

/-- Creates a Python string from a Lean string. -/
@[extern "nerodia_mk_py_str"]
public opaque mkPyStr (s : @& String) : CPyIO PyStr

public instance : MkCResult String .str := ⟨mkPyStr⟩

/-- Decodes a Lean {name}`ByteArray` into a Python string. -/
@[extern "nerodia_decode"]
public opaque decode (bytes : @& ByteArray)
  (encoding : @& Codec) (errors : @& CodecErrors := .strict) : CPyIO PyStr

/--
Decodes a bytes-like object into a string.

This is equivalent to the Python {lit}`str(self, encoding, errors)`.
-/
@[extern "nerodia_py_object_decode", view_method]
public opaque PyBuffer.decode (self : @& PyBuffer)
  (encoding : @& Codec) (errors : @& CodecErrors := .strict) : CPyIO PyStr

/--
Computes a string representation of the object {lean}`self`.

This is equivalent to the Python expression {lit}`str(self)`.
-/
@[extern "nerodia_py_object_str", view_method]
public opaque PyObject.str (self : @& PyObject) : CPyIO PyStr

/--
Computes a string representation of the object {lean}`self`.

This is equivalent to the Python expression {lit}`repr(self)`.
-/
@[extern "nerodia_py_object_repr", view_method]
public opaque PyObject.repr (self : @& PyObject) : CPyIO PyStr

/--
Returns the UTF8-encoded value of {lean}`self` as a Lean {lean}`String`.

If the string contains lone surrogates (and is thus not valid UTF-8),
they will be replaced with `�` (U+FFFD, the official Unicode replacement
character), following Lean's standard lossy encoding.
-/
-- This function is pure because the string data of instances of `str` is immutable.
@[extern "nerodia_py_str_to_string"]
public opaque PyStr.toString (self : @& PyStr) : String

public instance : ToString PyStr := ⟨PyStr.toString⟩

public instance : OfPyArg String .str where
  ofPyArg fn i o :=
    if h : o.isStrInstance then
      return (PyStr.mk o h).toString
    else raisePyTypeError s!"{fn} argument {i} must be str"

/--
Returns the string encoded as bytes.

This is equivalent to the Python {lit}`str.encode(self, encoding, errors)`.
-/
@[extern "nerodia_py_str_encode"]
public opaque PyStr.encode (self : @& PyStr)
  (encoding : @& Codec) (errors : @& CodecErrors := .strict) : CPyIO PyBytes

/--
Returns the UTF-8-encoded value of the string as bytes.

This is equivalent to {lean}`self.encode .utf8 .strict` but more efficient.
-/
@[extern "nerodia_py_str_encode_utf8"]
public abbrev PyStr.encodeUTF8 (self : @& PyStr) : CPyIO PyBytes :=
  self.encode .utf8 .strict

/-- Creates a Python {lit}`bytes` object from a Lean {name}`ByteArray`. -/
@[extern "nerodia_mk_py_bytes"]
public opaque mkPyBytes (s : @& ByteArray) : CPyIO PyBytes

namespace PyBytes

/-- Returns the bytes of {lean}`self` as a Lean {lean}`ByteArray`. -/
-- This function is pure because the bytes data of instances of `bytes` is immutable.
@[extern "nerodia_py_bytes_to_byte_array"]
public opaque toByteArray (self : @& PyBytes) : ByteArray

/-- Returns the number of bytes in {lean}`self` as a Lean {name}`USize`. -/
-- This function is pure because the bytes data of instances of `bytes` is immutable.
@[extern "nerodia_py_bytes_usize"]
public def usize (self : @& PyBytes) : USize :=
  self.toByteArray.usize

@[simp, grind =]
public theorem usize_eq : usize bs = bs.toByteArray.usize := by rfl

@[inline] public def sizeImpl (self : @& PyBytes) : Nat :=
  self.usize.toNat

/-- Returns the number of bytes in {lean}`self` as a Lean {name}`Nat`. -/
@[implemented_by sizeImpl]
public def size (self : @& PyBytes) : Nat :=
  self.toByteArray.size

@[simp, grind =]
public theorem size_eq : size bs = bs.toByteArray.size := by rfl

/--
Decodes bytes as a UTF-8-encoded string.

This is equivalent to {lean}`self.decode .utf8 .strict`.
-/
public abbrev decodeUTF8 (self : @& PyBytes) : CPyIO PyStr :=
  self.decode .utf8 .strict

end PyBytes

/-! ## Formatted Exceptions -/

/--
Formats the exception as a Lean string,
closely mirroring how Python would print it.
-/
@[view_method]
public def PyBaseException.sprint (e : PyBaseException) : PyBaseIO String := do
  -- Aims to mirror `print_exception`
  -- https://github.com/python/cpython/blob/v3.14.5/Python/pythonrun.c#L965
  -- TODO: include traceback & module name
  let ename ← id do
    let some n ← (← e.getType).getQualName.run?
      | return "<unknown>"
    return n.toString
  let estr ← id do
    let some s ← e.str.run?
      | return "<exception str() failed>"
    return s.toString
  return if estr.isEmpty then ename else s!"{ename}: {estr}"

namespace PyIO

/--
Runs the {lean}`PyIO` function in {lean}`IO`.

If a exeception is raised, it will formatted in the standard Python manner
(see {name}`PyBaseException.sprint`) and reported as an {lean}`IO.userError`.

This creates a new temporary Python context for the call.
As such, it should only be used when a Python context is not available.
For instance, this can be used in {lit}`main` to run a {lean}`PyIO` function.
It is also used to run {lean}`PyIO` in `#eval`.

**Example**
```lean
def main : IO Unit := do
  let pyVer ← Nerodia.PyIO.toIO do
    let sys ← Nerodia.import "sys"
    let ver ← sys.getAttrByString "version"
    ver.str
  IO.println pyVer.toString
```
-/
@[inline] public def toIO (x : PyIO α) : IO α := do
  let ctx ← PyContext.getOrInit
  (← x.runUnsafe? ctx).getDM do
    let e ← ctx.getRaisedException
    let e ← e.sprint.runUnsafe ctx
    throw (IO.userError e)

public instance : MonadEval PyIO IO := ⟨toIO⟩

end PyIO

namespace CPyIO

/--
Runs the {lean}`CPyIO` function in {lean}`IO`.
See {lean}`PyIO.toIO` for details.
-/
@[inline] public def toIO (x : CPyIO α) : IO α := do
  x.toPyIO.toIO

public instance : MonadEval CPyIO IO := ⟨toIO⟩

end CPyIO
