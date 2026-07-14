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
inductive PyObject.Kind
| type
| baseException
| str
| bytes
| module
deriving Nonempty, DecidableEq

/-- The logical model of a Python object. -/
structure PyObject.Model where
  addr : Addr
  hint : TypeExpr
  kind : PyObject.Kind
  /-- Represents all data not otherwise modelled. -/
  data : Dynamic
  deriving Nonempty

/--
A Python object. A [{lit}`PyObject`][1] pointer managed by Lean.

[1]: https://docs.python.org/3/c-api/structures.html#c.PyObject
-/
public structure PyObject where
  private ofModel ::
    private toModel : PyObject.Model
    deriving Nonempty

public abbrev TypePred : Type :=
  PyObject → Prop

public class ToTypeExpr (T : TypePred) where
  toTypeExpr : TypeExpr

public def TypePred.any : TypePred :=
  fun _ => True

/-- A typed Python object. -/
public structure Py (T : TypePred) extends PyObject where
  property : T toPyObject

public instance : CoeOut (Py T) PyObject := ⟨Py.toPyObject⟩

public class inductive NonemptyPy (T : TypePred) : Prop where
  | intro (o : PyObject) (h : T o) : NonemptyPy T

public instance [NonemptyPy T] : Nonempty (Py T) := by
  match (inferInstance : NonemptyPy T) with
  | .intro o h => exact ⟨Py.mk o h⟩

/-- A Python object of unkown type. -/
public abbrev PyAny := Py .any

namespace PyObject

/-- Returns the address of the Python object (not the Lean wrapper). -/
@[extern "nerodia_py_object_addr"]
public def addr (self : @& PyObject) : Addr :=
  self.toModel.addr

set_option linter.unusedVariables.funArgs false in
@[inline] unsafe def castImpl (ty : TypeExpr) (self : PyObject) : PyObject :=
  unsafeCast self

/--
Casts the object to the type indicating by the hint {lean}`ty`.

This weakly types the object, providing no strong guarantees.

This is akin to the Python {lit}`typing.cast(ty, self)`.
-/
@[implemented_by castImpl]
public def cast (ty : TypeExpr) (self : PyObject) : PyObject :=
  ⟨{self.toModel with hint := ty}⟩

end PyObject

/-!
## Builtin Types

Builtin Python types (e.g., {lit}`str`) are represented statically in Nerodia.
They have given specialized static types (e.g., {lit}`PyStr`), and the type check
for them is a pure function (e.g., {lit}`isStrInstance`). This is not strictly
in accordance with the Python specification, which leaves the mutability of an
object's type undefined.

In pratice, while CPython does permit type mutation (e.g., via {lit}`__class__`
and {lit}`__bases__` reasignment), it prevents reassignment between most builtin
types. Furthermore, CPython's implementation strongly assumes builtin type
confusion cannot happen.

Nerodia thus chooses to model them statically to make reasoning easier,
accepting the cost of a potential future breakage in the event of an unlikely,
massive Python refactor.
-/

noncomputable def PyObject.ofKind (k : Kind) : PyObject :=
  ⟨{Classical.ofNonempty (α := PyObject.Model) with kind := k}⟩

noncomputable def PyObject.isOfKind (self : @& PyObject) (k : Kind) : Bool :=
  self.toModel.kind == k

theorem NonemptyPy.of_kind {k : PyObject.Kind} : NonemptyPy (·.isOfKind k) :=
  .intro (.ofKind k) <| by simp [PyObject.ofKind, PyObject.isOfKind]

public def TypePred.subtype (T : TypePred) (U : TypePred) : TypePred :=
  fun o => T o ∧ U o

/-! ### type -/

/-- Returns whether this type is an instance of {lit}`type`. -/
@[extern "nerodia_py_object_is_type_instance"]
public def PyObject.isTypeInstance (self : @& PyObject) : Bool :=
  self.isOfKind .type

public def TypePred.type : TypePred :=
  (·.isTypeInstance)

public instance : NonemptyPy .type := .of_kind

/--
A Python type object.

An instance of {lit}`type` or one of its subclasses.
Equivalently, a [{lit}`PyTypeObject`][1] pointer managed by Lean.

[1]: https://docs.python.org/3/c-api/type.html#c.PyTypeObject
-/
public abbrev PyType := Py .type

@[inline] public def PyType.mk (o : PyObject) (h : o.isTypeInstance) : PyType :=
  ⟨o, h⟩

/-! ### BaseException -/

/-- Returns whether this type is an instance of {lit}`BaseException`. -/
@[extern "nerodia_py_object_is_base_exception_instance"]
public def PyObject.isBaseExceptionInstance (self : @& PyObject) : Bool :=
  self.isOfKind .baseException

public def TypeExpr.baseException : TypeExpr :=
  ⟨"BaseException"⟩

public def TypePred.baseException : TypePred :=
  (·.isBaseExceptionInstance)

public instance : NonemptyPy .baseException := .of_kind

/-- A instance of {lit}`BaseException` that satisfies {lean}`T`. -/
public abbrev TPyBaseException (T : TypePred) := Py (.subtype .baseException T)

/-- A Python base exception object. That is, an instance of {lit}`BaseException`. -/
public abbrev PyBaseException := TPyBaseException .any

@[inline] public def PyBaseException.mk (o : PyObject) (h : o.isBaseExceptionInstance) : PyBaseException :=
  ⟨o, ⟨h, .intro⟩⟩

public def TPyBaseException.toPyBaseException (self : TPyBaseException T) : PyBaseException :=
  ⟨self, ⟨self.property.1, .intro⟩⟩

public instance: CoeOut (TPyBaseException T) PyBaseException := ⟨TPyBaseException.toPyBaseException⟩

/-! ### str -/

/-- Returns whether this type is an instance of {lit}`str`. -/
@[extern "nerodia_py_object_is_str_instance"]
public def PyObject.isStrInstance (self : @& PyObject) : Bool :=
  self.isOfKind .str

public def TypePred.str : TypePred :=
  (·.isStrInstance)

public instance : NonemptyPy .str := .of_kind

/-- A Python unicode object. That is, an instance of {lit}`str`. -/
public abbrev PyStr := Py .str

@[inline] public def PyStr.mk (o : PyObject) (h : o.isStrInstance) : PyStr :=
  ⟨o, h⟩

/-! ### bytes -/

/-- Returns whether this type is an instance of {lit}`bytes`. -/
@[extern "nerodia_py_object_is_bytes_instance"]
public def PyObject.isBytesInstance (self : @& PyObject) : Bool :=
  self.isOfKind .bytes

public def TypePred.bytes : TypePred :=
  (·.isBytesInstance)

public instance : NonemptyPy .bytes := .of_kind

/-- A Python bytes object. That is, an instance of {lit}`bytes`. -/
public abbrev PyBytes := Py .bytes

@[inline] public def PyBytes.mk (o : PyObject) (h : o.isBytesInstance) : PyBytes :=
  ⟨o, h⟩

/-! ### types.ModuleType -/

/-- Returns whether this type is an instance of {lit}`types.ModuleType`. -/
@[extern "nerodia_py_object_is_module_instance"]
public def PyObject.isModuleInstance (self : @& PyObject) : Bool :=
  self.isOfKind .module

public def TypePred.module : TypePred :=
  (·.isModuleInstance)

public instance : NonemptyPy .module := .of_kind

/-- A Python module object. That is, an instance of {lit}`types.ModuleType`. -/
public abbrev PyModule := Py .module

@[inline] public def PyModule.mk (o : PyObject) (h : o.isModuleInstance) : PyModule :=
  ⟨o, h⟩

/-!
## BaseException Subtypes

Unlike {lit}`BaseException` itself, it is possible to mutate objects between
many of its subtypes (e.g., an object can be retyped to/from {lit}`Exception`).
As such, instances of these subtypes are weakly typed.
-/

public noncomputable def PyObject.IsHintedAs (ty : TypeExpr) (self : @& PyObject) : Prop :=
  self.toModel.hint = ty

public instance : NonemptyPy (·.IsHintedAs ty) :=
  .intro (.cast ty Classical.ofNonempty) <| by simp [PyObject.cast, PyObject.IsHintedAs]

public instance : NonemptyPy (.subtype .baseException (·.IsHintedAs ty)) :=
  .intro (.cast ty (.ofKind .baseException)) <| by
    simp [
      PyObject.cast, TypePred.subtype,
      TypePred.baseException, PyObject.isBaseExceptionInstance,
      PyObject.isOfKind, PyObject.ofKind, PyObject.IsHintedAs
    ]

/-- An instance of {lit}`BaseException` that is weakly typed as {lit}`ty`. -/
public abbrev HPyBaseException (ty : TypeExpr) := TPyBaseException (·.IsHintedAs ty)

/-! ### Exception -/

public def TypeExpr.exception : TypeExpr := ⟨"Exception"⟩

public abbrev TypePred.exception : TypePred :=
  baseException.subtype (·.IsHintedAs .exception)

/-- A weakly typed instance of {lit}`Exception`. -/
public abbrev PyException := HPyBaseException .exception

/-! ### SystemError -/

public def TypeExpr.systemError : TypeExpr := ⟨"SystemError"⟩

public abbrev TypePred.systemError : TypePred :=
  baseException.subtype (·.IsHintedAs .systemError)

/-- A weakly typed instance of {lit}`SystemError`. -/
public abbrev PySystemError := HPyBaseException .systemError

/-! ### TypeError -/

public def TypeExpr.typeError : TypeExpr := ⟨"TypeError"⟩

public abbrev TypePred.typeError : TypePred :=
  baseException.subtype (·.IsHintedAs .typeError)

/-- A weakly typed instance of {lit}`TypeError`. -/
public abbrev PyTypeError := HPyBaseException .typeError

/-! ## Builtin Constants -/

/-- Returns a reference to the {lit}`None` constant. -/
@[extern "nerodia_none"]
public opaque PyEnvironment.none (env : @& PyEnvironment) : PyObject

@[extern "nerodia_none", inherit_doc PyEnvironment.none]
public abbrev PyContext.none (ctx : @& PyContext) : PyObject :=
  ctx.env.none

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
public structure CPyBaseResult (α : Type u) extends toCPtrUnsafe : CPtr α where
  /--
  Constructs a {name}`CPyBaseResult` from a raw Python object pointer,
  with both sharing the strong reference.

  **Memory Safety:** Users must ensure the pointer is a strong reference
  and manually manage the reference's lifetime.
  -/
  private ofCPtrUnsafe ::
    deriving Nonempty, DecidableEq


/--
Converts the {name}`CPyBaseResult` to a raw Pyton object pointer,
with both sharing the strong reference.

**Memory Safety:** Users must manually manage the reference's lifetime.
-/
add_decl_doc CPyBaseResult.toCPtrUnsafe

/-! ## CPyResult -/

/--
The result of a Python C API function returning a Python object.

Implementation-wise, this is either {lit}`NULL` or a raw strong reference
to a Python object. {lit}`NULL` indicates an exception has been raised.

**Not memory safe.** The result's lifetime must be manually managed.
It is not managed by Lean. Nerodia handles this within its API, and users are
not expected to manage {name}`CPyResult` objects manually.
-/
public structure CPyResult (α : Type u) extends toNullableCPtrUnsafe : NullableCPtr α where
  /--
  Constructs a result from a raw Python object pointer
  (or {name}`null`), with both sharing the strong reference.

  **Safety**
  * **Correctness:** Users should ensure that an exception is set if {name}`null`.
  * **Memory:** Users must ensure the pointer is a strong reference
  and manually manage the reference's lifetime.
  -/
  private ofNullableCPtrUnsafe ::
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
  .ofNullableCPtrUnsafe o.toCPtrUnsafe

/--
Constructs a {lean}`CPyResult` indicating failure.

**Safety:** Users should ensure that an exception is set.
-/
@[inline] public def failureUnsafe : CPyResult α :=
  ⟨null⟩

public instance : Inhabited (CPyResult α) := ⟨failureUnsafe⟩

public abbrev IsFailure (self : CPyResult α) : Prop :=
  self.IsNull

/--
Constructs a {name}`CPyBaseResult` from a successful {name}`CPyResult`,
sharing the single strong reference between them.

**Memory Safety:** Users must manually manage the reference's lifetime.
-/
@[inline] def toCPyBaseResultUnsafe (self : CPyResult α) (h : ¬ self.IsFailure) : CPyBaseResult α :=
  .ofCPtrUnsafe (.ofNullableCPtr self.toNullableCPtrUnsafe h)

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
* **Memory:** Users must ensure that a rturned object reference is consumed,
and that it  does not outlive the enviroment.
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

/-- Converts a {lean}`CPyIO` returning a typed Python object into untyped general object. -/
@[inline] public def cast (x : CPyIO α) : CPyIO PyObject :=
  unsafe unsafeCast x

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
def PyObject.newRef (self : @& PyObject) : CPyBaseIO PyObject :=
  .ofBaseIOUnsafe <| pure <| .ofCPtrUnsafe (.ofAddrNoncomputable self.addr)

namespace CPyBaseIO

/-- Constructs a {lean}`CPyBaseIO` that returns {lean}`o`. -/
@[inline] public protected def pure (o : PyObject) : CPyBaseIO PyObject :=
  o.newRef

public instance [Nonempty α] : Nonempty (CPyBaseIO α) :=
  ⟨ofBaseIOUnsafe <| pure <| Classical.ofNonempty⟩

end CPyBaseIO

/-- Constructs a successful {lean}`CPyIO` that returns {lean}`o`. -/
@[inline] public protected abbrev CPyIO.pure (o : PyObject) : CPyIO PyObject :=
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
@[inline] public def PyBaseIO.toCPyBaseIO (x : PyBaseIO PyObject) : CPyBaseIO PyObject :=
  x.bindCPyBaseIO CPyBaseIO.pure

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
@[inline] public def PyIO.toCPyIO (x : PyIO PyObject) : CPyIO PyObject :=
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

public class ToBaseException (ε : Type u) where
  toBaseException (e : ε) : PyBaseException

public instance : ToBaseException PyBaseException := ⟨(·)⟩
public instance : ToBaseException PyException := ⟨(·)⟩
public instance : ToBaseException PySystemError := ⟨(·)⟩
public instance : ToBaseException PyTypeError := ⟨(·)⟩

 /-- Raises the exception {lean}`e`.-/
@[inline] public def raise [MonadRaise m] [ToBaseException ε] (e : ε) : m α :=
  MonadRaise.raise (ToBaseException.toBaseException e)

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

/-! ## CPyArg -/

/--
A raw Python function argument (a borrowed Python object reference).

**Not memory safe.** The reference must not escape the function.
This is not managed by Lean. Nerodia handles this within its API, and users are
not expected to manage {name}`TCPyArg` objects manually.
-/
public structure TCPyArg (α : Type u) where
  private ofCPtrUnsafe ::
    private toCPtrUnsafe : CPtr α

@[inherit_doc TCPyArg]
public abbrev CPyArg := TCPyArg PyObject

/--
Wraps a borrowed Python object reference into a memory-managed Lean object.

**Memory Safety:** Users must ensure the reference currently valid
(e.g., it has not escaped its original function).
-/
@[extern "nerodia_py_context_mk_arg"]
def PyContext.mkArgUnsafe (ctx : @& PyContext) (arg : TCPyArg α) : α :=
  Classical.choice arg.toCPtrUnsafe.nonempty

/--
A raw C pointer array of Python function arguments
(borrowed Python object references).

**Not memory safe.** The references must not escape the function.
This is not managed by Lean. Nerodia handles this within its API, and users are
not expected to manage {name}`TCPyArg` objects manually.
 -/
public structure CPyArgs where
  private ofAddrUnsafe ::
    private addr : Addr

@[extern "nerodia_py_context_mk_args"]
opaque PyContext.mkArgsUnsafe (ctx : @& PyContext) (args : CPyArgs) (nargs : USize) : Array PyObject

@[extern "nerodia_py_context_mk_nth_arg"]
opaque PyContext.mkNthArgUnsafe (ctx : @& PyContext) (args : CPyArgs) (i : USize) : PyObject

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
  (self : CPyArg) → Null → CPyIO PyObject

@[inline] public def PyMethNoArgs.ofPyIO
  (x : (self : PyObject) → PyIO PyObject)
: PyMethNoArgs := fun self _ => PyIO.toCPyIO do
  let ctx ← getPyContextUnsafe
  let self := ctx.mkArgUnsafe self
  x self

@[inline] public def PyMethNoArgs.ofPyIO'
  (x : PyIO PyObject)
: PyMethNoArgs := ofPyIO fun _ => x

@[inline] public def PyMethNoArgs.ofCPyIO
  (x : CPyIO PyObject)
: PyMethNoArgs := fun _ _ => x

/-- The type of a Python method with a single positional argument. -/
@[expose] -- for codegen
public def PyMethFastCall :=
  (self : CPyArg) → (args : CPyArgs) → (nargs : USize) → CPyIO PyObject

@[inline] public def PyMethFastCall.ofPyIO
  (x : (self : PyObject) → (args : Array PyObject) → PyIO PyObject)
: PyMethFastCall := fun self args nargs => PyIO.toCPyIO do
  let ctx ← getPyContextUnsafe
  let self := ctx.mkArgUnsafe self
  let args := ctx.mkArgsUnsafe args nargs
  x self args

/-- **Do not use.** Internal function for {lit}`@[py_module_fn]`. -/
@[inline] public def Internal.mkPyMethFastCallUnsafe
  (fn : String) (arity : USize)
  (x : (args : CPyArgs) → CPyIO PyObject)
: PyMethFastCall := fun _ args nargs =>
  if nargs = arity then
    x args
  else
    raiseArityNotEq fn arity nargs

/-- The type of a Python method with a single positional argument. -/
@[expose] -- for codegen
public def PyMethO :=
  (self : CPyArg) → (arg : CPyArg) → CPyIO PyObject

@[inline] public def PyMethO.ofPyIO
  (x : (self : PyObject) → (arg : PyObject) → PyIO PyObject)
: PyMethO := fun self arg => PyIO.toCPyIO do
  let ctx ← getPyContextUnsafe
  let self := ctx.mkArgUnsafe self
  let arg := ctx.mkArgUnsafe arg
  x self arg

@[inline] public def PyMethO.ofPyIO'
  (x : (arg : PyObject) → PyIO PyObject)
: PyMethO := ofPyIO fun _ => x

/-- The type of a Python module initialization function. -/
@[expose] -- for codegen
public def PyModuleInit :=
  (mod : TCPyArg PyModule) → CPyUnitIO

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
@[extern "nerodia_py_object_get_type"]
public opaque PyObject.getType (self : @& PyObject) : CPyBaseIO PyType

/-! ## Module -/

/--
Imports the module named {lean}`modName`.

In Python, the import can be anything, so this may not return a {lean}`PyModule`.
-/
@[extern "nerodia_import"]
public opaque «import» (modName : @& String) : CPyIO PyObject

namespace PyModule

/-- Adds an object {lean}`val` to the module {lean}`self` as {lean}`name`. -/
@[extern "nerodia_py_module_add_by_string"]
public opaque addByString (name : @& String) (val : @& PyObject) (self : @& PyModule) : CPyUnitIO

end PyModule

/-- Returns the {lit}`None` constant of the Python environment. -/
@[inline] public def getPyNone [Functor m] [MonadPyEnv m] : m PyObject :=
  (·.none) <$> getPyEnvironment

/-- Returns the {lit}`None` constant of the Python environment. -/
@[inline] public def getCPyNone : CPyBaseIO PyObject :=
  PyBaseIO.toCPyBaseIO getPyNone

/--
Type class used to construct a Lean object from a Python function argument.

Used by {lit}`@[py_module_fn]`.
-/
public class OfPyArg (α : Type) (ty : outParam String) where
  ofPyArg (fn : String) (i : Nat) : PyObject → PyIO α

/-- **Do not use.** Internal function for {lit}`@[py_module_fn]`.  -/
@[inline] public def Internal.ofPyArgUnsafe
  [OfPyArg α ty] (fn : String) (i : USize) (args : CPyArgs) : PyIO α
:= do OfPyArg.ofPyArg fn (i.toNat+1) ((← getPyContextUnsafe).mkNthArgUnsafe args i)

/--
Type class used to construct Python return values from Lean objects.

Used by {lit}`@[py_module_fn]` and {lit}`@[py_module_attr]`.
-/
public class MkResult (α : Type u) (ty : outParam String) where
  mkResult : α → CPyIO PyObject

public instance : MkResult PUnit "None" where
  mkResult _ := getCPyNone

public instance [MkResult α ty] : MkResult (BaseIO α) ty where
  mkResult x := .ofBind x MkResult.mkResult

public instance [MkResult α ty] : MkResult (PyIO α) ty where
  mkResult x := x.bindCPyIO MkResult.mkResult

public abbrev PyAttrInit := CPyIO PyObject

/-! ## Objects -/

/-- Returns the attribute named {lean}`attrName` on {lean}`self`. -/
@[extern "nerodia_py_object_get_attr_by_string"]
public opaque PyObject.getAttrByString
  (self : @& PyObject) (attrName : @& String) : CPyIO PyObject


/-! ## Strings & ByteArray -/

/-- Creates a Python string from a Lean string. -/
@[extern "nerodia_mk_py_str"]
public opaque mkPyStr (s : @& String) : CPyIO PyStr

public instance : MkResult String "str" := ⟨(mkPyStr · |>.cast)⟩

/-- Decodes a Lean {name}`ByteArray` into a Python string. -/
@[extern "nerodia_decode"]
public opaque decode (bytes : @& ByteArray)
  (encoding : @& Codec) (errors : @& CodecErrors := .strict) : CPyIO PyStr

/--
Decodes a bytes-like object into a string. All other objects raise a {lit}`TypeError`.

This is equivalent to the Python {lit}`str(self, encoding, errors)`.
-/
@[extern "nerodia_py_object_decode"]
public opaque PyObject.decode (self : @& PyObject)
  (encoding : @& Codec) (errors : @& CodecErrors := .strict) : CPyIO PyStr

/--
Computes a string representation of the object {lean}`self`.

This is equivalent to the Python expression {lit}`str(self)`.
-/
@[extern "nerodia_py_object_str"]
public opaque PyObject.str (self : @& PyObject) : CPyIO PyStr

/--
Computes a string representation of the object {lean}`self`.

This is equivalent to the Python expression {lit}`repr(self)`.
-/
@[extern "nerodia_py_object_repr"]
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

public instance : OfPyArg String "str" where
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

public instance : MkResult ByteArray "bytes" := ⟨(mkPyBytes · |>.cast)⟩

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

/-- Decodes bytes as a string. -/
@[inline] public def decode
  (self : @& PyBytes)
  (encoding : @& Codec) (errors : @& CodecErrors := .strict)
: CPyIO PyStr := self.toPyObject.decode encoding errors

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
