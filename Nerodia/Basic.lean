/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.CPtr

/-! # Nerodia -/

namespace Nerodia

/-! ## PyEnvironment -/

/--
Reference holder for the Python environment.

Python objects created by Nerodia implicitly hold a reference to the Python
environment. Thus, the Python environment will not be finalized until all Python
objects managed by Lean are freed.
-/
public structure PyEnvironment where
  private mk ::
    private data : Dynamic
    deriving Nonempty

namespace PyEnvironment

/--
Returns a reference to the Python environment.

If no Python environment exists yet, it will be initialized.
-/
@[extern "nerodia_py_environment_get_or_init"]
public opaque getOrInit : BaseIO PyEnvironment

end PyEnvironment

/-! ## PyContext -/

structure PyContext.Model where
  mk ::
    env : PyEnvironment
    data : Dynamic
    deriving Nonempty

/--
Reference holder for the Python environment ({name}`PyEnvironment`)
and the global interpreter lock (GIL).

**Not thread safe.** As a {name}`PyContext` object holds a lock (the GIL),
it must not be marked persistent or multi-threaded. Any attempt to do so
will emit a fatal panic. Nerodia ensures this within its API, and users are
not expected to manage {name}`PyContext` objects manually.
-/
public structure PyContext where
  private ofModel ::
    private toModel : PyContext.Model
    deriving Nonempty

namespace PyContext

noncomputable opaque mkOpaque (env : PyEnvironment) : BaseIO PyContext

/--
Constructs a Python context from a Python environment,
ensuring this thread has the global interpreter lock (GIL).
-/
@[extern "nerodia_py_context_mk"]
public def mk (env : @& PyEnvironment) : BaseIO PyContext :=
  (ofModel {·.toModel with env}) <$> mkOpaque env

/--
Returns a reference to this thread's Python context,
ensuring the thread has the global interpreter lock (GIL).

If no Python environment exists yet, it will be initialized.
-/
@[extern "nerodia_py_context_get_or_init"]
public def getOrInit : BaseIO PyContext := do
  mk (← PyEnvironment.getOrInit)

/-- Returns a reference to the Python environment. -/
@[extern "nerodia_py_context_env"]
public def env (ctx : @& PyContext) : PyEnvironment :=
  ctx.toModel.env

end PyContext

/-! ## PyObject -/

/--
A Python object.

See https://docs.python.org/3/c-api/structures.html#c.PyObject
-/
public structure PyObject where
  private mk ::
    private impl : NonScalar
    deriving Nonempty

namespace PyObject

/-- Returns the address of the Python object (not the Lean wrapper). -/
@[extern "nerodia_py_object_addr"]
public opaque addr (self : @& PyObject) : Addr

/-!
### Builtin Type Checking

These functions are considered pure even though the Python specification
leaves the mutability of type inheritance undefined. In practice, CPython does
sometimes allow subtypes to have their {lit}`__bases__` reassigned and thus
mutate away inheritance (and further relaxes the constraints on this in 3.15).
However, it prevents reassignments between builtin types and heavily relies
on the fact that type confusion between builtin types cannot happen.

Thus, Nerodia chooses to model these as pure to make reasoning easier,
accepting the cost of a potential future breakage in the event of an unlikely,
massive Python refactor.
-/

/-- Returns whether this type is an instance of {lit}`type`. -/
@[extern "nerodia_py_object_is_type_instance"]
public opaque isTypeInstance (self : @& PyObject) : Bool

/-- Returns whether this type is an instance of {lit}`str`. -/
@[extern "nerodia_py_object_is_str_instance"]
public opaque isStrInstance (self : @& PyObject) : Bool

end PyObject

/-! ## Builtin Types -/

/--
A Python type object.

In practice, these are instances of {lit}`type` or one of its subclasses,
but that is not guaranteed by the Limited API.

See https://docs.python.org/3/c-api/type.html#c.PyTypeObject
-/
public structure PyType extends PyObject where
  private innerMk ::
    deriving Nonempty

public instance : Coe PyType PyObject := ⟨PyType.toPyObject⟩

/-- A Python base exception object. That is, an instance of {lit}`BaseException`. -/
public structure PyBaseException extends PyObject where
  private innerMk ::
    deriving Nonempty

/-- A Python exception object. That is, an instance of {lit}`Exception`. -/
public structure PyException extends PyBaseException where
  private innerMk ::
    deriving Nonempty

public instance : Coe PyException PyBaseException :=
  ⟨PyException.toPyBaseException⟩

/-- A Python system error object. That is, an instance of {lit}`SystemError`. -/
public structure PySystemError extends PyException where
  private innerMk ::
    deriving Nonempty

public instance : Coe PySystemError PyException :=
  ⟨PySystemError.toPyException⟩

/-- A Python type error object. That is, an instance of {lit}`TypeError`. -/
public structure PyTypeError extends PyException where
  private innerMk ::
    deriving Nonempty

public instance : Coe PyTypeError PyException :=
  ⟨PyTypeError.toPyException⟩

/-- A Python module object. That is, an instance of {lit}`types.ModuleType`. -/
public structure PyModule extends PyObject where
  private innerMk ::
    deriving Nonempty

/-- A Python unicode object. That is, an instance of {lit}`str`. -/
public structure PyStr extends PyObject where
  private innerMk ::
    deriving Nonempty

public instance : Coe PyStr PyObject := ⟨PyStr.toPyObject⟩

set_option linter.unusedVariables.funArgs false in
@[inline] public def PyStr.mk (o : PyObject) (h : o.isStrInstance) : PyStr :=
  ⟨o⟩

/-- A Python bytes object. That is, an instance of {lit}`bytes`. -/
public structure PyBytes extends PyObject where
  private innerMk ::
    deriving Nonempty

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
not expected to manage {name}`CPy` objects manually.
-/
public structure CPy (α : Type u) extends toCPtrUnsafe : CPtr α where
  /--
  Constructs a {name}`CPy` from a raw Python object pointer,
  with both sharing the strong reference.

  **Memory Safety:** Users must ensure the pointer is a strong reference
  and manually manage the reference's lifetime.
  -/
  private ofCPtrUnsafe ::
    deriving Nonempty, DecidableEq


/--
Converts the {name}`CPy` to a raw Pyton object pointer,
with both sharing the strong reference.

**Memory Safety:** Users must manually manage the reference's lifetime.
-/
add_decl_doc CPy.toCPtrUnsafe

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

/--
Wraps a strong Python object reference into a memory-managed Lean object,
stealing the reference.

**Memory Safety:** {lean}`o` is now borrowed, so its reference must not be
consumed and uses must not outlive the returned Lean object.
-/
@[extern "nerodia_mk_object"]
public opaque PyEnvironment.mkObjectUnsafe (env : @& PyEnvironment) (o : CPy α) : α :=
  Classical.choice o.nonempty

@[extern "nerodia_mk_object", inherit_doc PyEnvironment.mkObjectUnsafe]
public abbrev PyContext.mkObjectUnsafe (ctx : @& PyContext) (o : CPy α) : α :=
  ctx.env.mkObjectUnsafe o

/--
Returns a new strong reference to Python object's raw unmanaged C pointer.

**Memory Safety:** Users must ensure the reference is eventually consumed.
-/
@[extern "nerodia_py_object_new_ref"]
def PyObject.newRefUnsafe (self : @& PyObject) : CPy PyObject :=
  .ofCPtrUnsafe (.ofAddrNoncomputable self.addr)

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
@[inline] def ofCPyUnsafe (o : CPy α) : CPyResult α :=
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
Constructs a {name}`CPy` from a successful {name}`CPyResult`,
sharing the single strong reference between them.

**Memory Safety:** Users must manually manage the reference's lifetime.
-/
@[inline] def toCPyUnsafe (self : CPyResult α) (h : ¬ self.IsFailure) : CPy α :=
  .ofCPtrUnsafe (.ofNullableCPtr self.toNullableCPtrUnsafe h)

end CPyResult

@[inline, inherit_doc PyEnvironment.mkObjectUnsafe]
public def PyContext.mkResultUnsafe (ctx : @& PyContext) (r : CPyResult α) (h : ¬ r.IsFailure) : α :=
  ctx.env.mkObjectUnsafe (r.toCPyUnsafe h)

/-! ## MonadPy -/

/-- Type class of monads equipped with a Python environment. -/
public class MonadPyEnv (m : Type → Type u) where
  getPyEnvironment : m PyEnvironment

export MonadPyEnv (getPyEnvironment)

public instance [MonadLift m n] [MonadPyEnv m] : MonadPyEnv n where
  getPyEnvironment := liftM (m := m) getPyEnvironment

/-- Type class of monads equipped with a Python context. -/
public class MonadPy (m : Type → Type u) where
  /--
  Returns the Python context of the monad.

  **Thread Safety:** Users must ensure the {name}`PyContext` does
  not cross thread boundaries.
  -/
  getPyContextUnsafe : m PyContext

export MonadPy (getPyContextUnsafe)

public instance [MonadLift m n] [MonadPy m] :MonadPy n where
  getPyContextUnsafe := liftM (m := m) getPyContextUnsafe

public instance [Functor m] [MonadPy m] : MonadPyEnv m where
  getPyEnvironment := (·.env) <$> getPyContextUnsafe

/-- Returns the {lit}`None` constant of the Python enviroment. -/
@[inline] public def getPyNone [Functor m] [MonadPyEnv m] : m PyObject :=
  (·.none) <$> getPyEnvironment

/-! ## Monad Types -/

/-
Any definition that signals an exception without handling it is unsafe.
Python [expects][1] exceptions to be handled and [requires][2] that futher
Python functions are not called while an exception is set.

[1]: https://docs.python.org/3/c-api/exceptions.html#exception-handling
[2]: https://github.com/python/cpython/issues/67759

Definitions that signal an exception without setting are also unsafe.
While CPython [will][3] set its own exception if an FFI call returns `NULL`
without setting one, relying on this would be contray to the specification.

[3]: https://github.com/python/cpython/blob/v3.14.5/Objects/call.c#L31-L46
-/

/-- The primary monad for impure code using Python. -/
@[expose] -- for codegen
public def PyIO (α) :=
  ReaderT PyContext BaseIO (Option α)

namespace PyIO

/--
Constructs a {lean}`PyIO` from its definition.

**Safety:** Users should ensure that an exception is set on {lean}`x`'s failure.
-/
@[inline] def mkUnsafe (x : ReaderT PyContext (OptionT BaseIO) α) : PyIO α :=
  x

/--
Runs the {lean}`PyIO` function, returning {lean}`none` if an exception was raised.

**Safety**
* **Correctness:** Users must handle a raised exception.
* **Thread:** Users must ensure that {lean}`ctx` does not cross thread boundaries.
-/
@[inline] def runUnsafe? (ctx : PyContext) (x : PyIO α) : BaseIO (Option α) :=
  x ctx

@[inline, inherit_doc getPyContextUnsafe]
public protected def getPyContextUnsafe : PyIO PyContext :=
  mkUnsafe read

public instance : MonadPy PyIO := ⟨PyIO.getPyContextUnsafe⟩

/--
Constructs a {lean}`PyIO` that fails.

**Safety:** Users should ensure that an exception is set.
-/
@[inline] def failureUnsafe : PyIO α :=
  mkUnsafe failure

@[inline, inherit_doc pure]
public protected def pure (a : α) : PyIO α :=
  mkUnsafe <| pure a

public instance : Pure PyIO := ⟨PyIO.pure⟩

@[inline, inherit_doc Functor.map]
public protected def map (f : α → β) (x : PyIO α) : PyIO β :=
  mkUnsafe <| Functor.map f x

public instance : Functor PyIO where map := PyIO.map

@[inline, inherit_doc bind]
public protected def bind (x : PyIO α) (f : α → PyIO β) : PyIO β :=
  mkUnsafe <| bind x f

-- Internally used by `@[py_module_fn]`
public instance : Bind PyIO := ⟨PyIO.bind⟩

public instance : Monad PyIO := {}

end PyIO

/-- A monad for impure code using Python. Unlike {lean}`PyIO`, it cannot error. -/
@[expose] -- for codegen
public def PyBaseIO :=
  ReaderT PyContext BaseIO

namespace PyBaseIO

/--
Constructs a {lean}`PyBaseIO` from its definition.

**Thread Safety:** Users must ensure the {lean}`PyContext` does not cross
thread boundaries.
-/
@[inline] public def mkUnsafe (x : ReaderT PyContext BaseIO α)  : PyBaseIO α :=
  x

@[inline] public def ofBaseIO (x : BaseIO α)  : PyBaseIO α :=
  mkUnsafe x

public instance : MonadLift BaseIO PyBaseIO := ⟨ofBaseIO⟩

/--
Runs the action within the given Python context.

**Thread Safety:** Users must ensure {lean}`ctx` does not cross thread boundaries.
-/
@[inline] public def runUnsafe (ctx : PyContext) (x : PyBaseIO α)  : BaseIO α :=
  x.run ctx

/-- Runs the action within the given Python environment. -/
@[inline] public def run (env : PyEnvironment) (x : PyBaseIO α) : BaseIO α := do
  x.runUnsafe (← PyContext.mk env)

@[inline] public def toPyIO (x : PyBaseIO α) : PyIO α := .mkUnsafe fun ctx =>
  liftM <| x.runUnsafe ctx

public instance : MonadLift PyBaseIO PyIO := ⟨toPyIO⟩

@[inline] public nonrec def toBaseIO (x : PyBaseIO α) : BaseIO α := do
  x.runUnsafe (← PyContext.getOrInit)

public instance : MonadEval PyBaseIO BaseIO := ⟨PyBaseIO.toBaseIO⟩

@[inline, inherit_doc getPyContextUnsafe]
public protected def getPyContextUnsafe : PyBaseIO PyContext :=
  mkUnsafe read

public instance : MonadPy PyBaseIO := ⟨PyBaseIO.getPyContextUnsafe⟩

@[inline, inherit_doc pure]
public protected def pure (a : α) : PyBaseIO α :=
  mkUnsafe <| pure a

public instance : Pure PyBaseIO := ⟨PyBaseIO.pure⟩

@[inline, inherit_doc Functor.map]
public protected def map (f : α → β) (x : PyBaseIO α) : PyBaseIO β :=
  mkUnsafe <| Functor.map f x

public instance : Functor PyBaseIO where map := PyBaseIO.map

@[inline, inherit_doc bind]
public protected def bind (x : PyBaseIO α) (f : α → PyBaseIO β) : PyBaseIO β :=
  mkUnsafe <| bind x f

public instance : Bind PyBaseIO := ⟨PyBaseIO.bind⟩

public instance : Monad PyBaseIO := {}

end PyBaseIO

/--
Return context for external CPython functions.

Not a monad itself, but lifts into monads equipped with a Python environment.
-/
@[expose] -- for codegen
public def CPyIO (α) :=
  BaseIO (CPyResult α)

namespace CPyIO

/-- Constructs a {lean}`CPyIO` function from its definition.  -/
@[inline] public def mkUnsafe (x : BaseIO (CPyResult α)) : CPyIO α :=
  x

/--
Runs the {lean}`CPyIO` function, returning the raw, unmanaged pointer.

**Memory Safety:** Users must ensure a Python environment exists
and that the returned pointer does not outlive it.
-/
@[inline] def runUnsafe (x : CPyIO α) : BaseIO (CPyResult α) :=
  x

/-- Constructs a successful {lean}`CPyIO` that returns {lean}`o`. -/
@[inline] def ok (o : PyObject) : CPyIO PyObject :=
  mkUnsafe <| pure <| .ofCPyUnsafe o.newRefUnsafe

/--
Constructs a {lean}`CPyIO` that fails.

**Safety:** Users should ensure that an exception is set.
-/
@[inline] def failureUnsafe : CPyIO α :=
  mkUnsafe <| pure .failureUnsafe

public instance : Nonempty (CPyIO α) := ⟨failureUnsafe⟩

/-- Converts a {lean}`CPyIO` returning a typed Python object into untyped general object. -/
@[inline] public def cast (x : CPyIO α) : CPyIO PyObject :=
  unsafe unsafeCast x

end CPyIO

/--
Runs a {lean}`PyIO` action producing a Python object in {lean}`CPyIO`.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyIO.toCPyIO (x : PyIO PyObject) : CPyIO PyObject := .mkUnsafe do
  let ctx ← PyContext.getOrInit
  match ( ← x.runUnsafe? ctx) with
  | some obj => CPyIO.ok obj
  | none => CPyIO.failureUnsafe

/--
Sequences a {lean}`CPyIO` action after a {lean}`PyIO` action.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyIO.bindCPyIO (x : PyIO α) (f : α → CPyIO β) : CPyIO β := .mkUnsafe do
  let ctx ← PyContext.getOrInit
  match (← x.runUnsafe? ctx) with
  | some a => f a
  | none => CPyIO.failureUnsafe


/--
Return type for external CPython functions that may error but do not return
a Python object.
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

/-- Clears the current exception and returns it. -/
@[extern "nerodia_get_raised_exception"]
opaque getRaisedException : CPyIO PyBaseException

/--
Constructs a {lit}`SystemError` with the string {lean}`msg`.
Panics if the construction fails (e.g., due to lack of memeory).
-/
@[extern "nerodia_py_context_system_error"]
opaque PyContext.systemError! (msg : @& String) (ctx : @& PyContext) : PySystemError

/-- The exception used when when no other exception is set. -/
@[inline] public opaque PyContext.unsetException (ctx : PyContext) : PySystemError :=
  ctx.systemError! "no exception was set"

/-- Returns the currently raised exception or {name}`unsetException` if none. -/
@[inline] public protected def PyContext.getRaisedException
  (ctx : PyContext)
: BaseIO PyBaseException := do
  let res ← getRaisedException.runUnsafe
  if h : res.IsFailure then
    return ctx.unsetException
  else
    return ctx.mkResultUnsafe res h

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
    let e ← ctx.getRaisedException
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
: m α := do
  let ctx ← getPyContextUnsafe
  let res ← x.runUnsafe
  if h : res.IsFailure then
    throw (← ctx.getRaisedException)
  else
    return ctx.mkResultUnsafe res h

/--
Runs the {lean}`CPyIO` function in a supporting monad
If a Python error occurs, it is set as the exception.
-/
public abbrev toExceptT
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m] (x : CPyIO α)
: ExceptT PyBaseException m α := x.run

/-- Lifts the {lean}`CPyIO` function into {lean}`PyIO`, reusing its Python context. -/
@[inline] public def toPyIO (x : CPyIO α) : PyIO α := do
  let ctx ← getPyContextUnsafe
  let res ← x.runUnsafe
  if h : res.IsFailure then
    .failureUnsafe
  else
    return ctx.mkResultUnsafe res h

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
: m α := do
  let ctx ← getPyContextUnsafe
  let res ← x.runUnsafe
  if h : res.IsFailure then
    ctx.clearError
    failure
  else
    return ctx.mkResultUnsafe res h

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
@[inline] public protected def raise (e : PyBaseException) : CPyIO α := .mkUnsafe do
  setRaisedExceptionUnsafe e
  CPyIO.failureUnsafe

public instance : MonadRaise CPyIO := ⟨CPyIO.raise⟩

@[inline] public protected def tryCatch
  [Monad m] [MonadLiftT BaseIO m] [MonadPy m]
  (x : CPyIO α) (f : PyBaseException → m α)
: m α := do
  let ctx ← getPyContextUnsafe
  let res ← x.runUnsafe
  if h : res.IsFailure then
    f (← ctx.getRaisedException)
  else
    return ctx.mkResultUnsafe res h

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
@[inline] public def raisePyTypeError (msg : String) : CPyIO α := .mkUnsafe do
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
-- TODO: Return should really be `CPyBaseIO`
@[extern "nerodia_py_object_get_type"]
public opaque PyObject.getType (self : @& PyObject) : PyBaseIO PyType

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

-- TODO: Should be `CPyBaseIO`
@[inline] public def getCPyNone : CPyIO PyObject := .mkUnsafe do
  CPyIO.ok (← PyContext.getOrInit).none

public instance : MkResult PUnit "None" where
  mkResult _ := getCPyNone

public instance [MkResult α ty] : MkResult (BaseIO α) ty where
  mkResult x := private .mkUnsafe do MkResult.mkResult (← x)

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

/-- Identifier of a registered Python encoding. -/
public structure Codec where
  ofString ::
    protected toString : String

namespace Codec

public instance : ToString Codec := ⟨Codec.toString⟩

/-!
### Standard Python Encodings

The Lean names of these Python identifiers follow Lean naming conventions
(i.e., lower camel case).

See the [Python documentation][1] for a for a full list of codecs and
what languages they support.

[1]: https://docs.python.org/3/library/codecs.html#standard-encodings
-/

public abbrev ascii : Codec := ⟨"ascii"⟩
public abbrev latin1 : Codec := ⟨"latin_1"⟩
public abbrev utf8 : Codec := ⟨"utf-8"⟩
public abbrev utf16 : Codec := ⟨"utf-16"⟩
public abbrev utf16LE : Codec := ⟨"utf-16-le"⟩
public abbrev utf16BE : Codec := ⟨"utf-16-be"⟩
public abbrev utf32 : Codec := ⟨"utf-32"⟩
public abbrev utf32LE : Codec := ⟨"utf-32-le"⟩
public abbrev utf32BE : Codec := ⟨"utf-32-be"⟩

end Codec

/-- Identifier of a registed Python error handler for codecs. -/
public structure CodecErrors where
  ofString ::
    protected toString : String

namespace CodecErrors

public instance : ToString CodecErrors := ⟨CodecErrors.toString⟩

/-!
### Standard Python Error Handlers

The Lean names of these Python identifiers follow Lean naming conventions
(i.e., lower camel case).
-/

/-- Raise {lit}`UnicodeError` (or a subclass). -/
public abbrev strict : CodecErrors := ⟨"strict"⟩

/-- Ignore the malformed data and continue without further notice. -/
public abbrev ignore : CodecErrors := ⟨"ignore"⟩

/--
Replace unspported characters with a replacement marker. On encoding,
use `?` (the ASCII character). On decoding, use `�` (U+FFFD, the official
Unicode replacement character).
-/
public abbrev replace : CodecErrors := ⟨"replace"⟩

/--
Replace unspported characters with backslashed escape sequences.
On encoding,  use hexadecimal form of Unicode code point with formats
{lit}`\xhh`, {lit}`\uxxxx`, {lit}`\Uxxxxxxxx`. On decoding, use hexadecimal
form of byte value with format {lit}`\xhh`.
-/
public abbrev backslashReplace : CodecErrors := ⟨"backslashreplace"⟩

/--
On decoding, replace surrogates with their individual surrogate escape
code ranging from {lit}`U+DC80` to {lit}`U+DCFF`. This code will then be turned
back into the surrogate when the {name}`surrogateEscape` error handler is
used when encoding the data.
-/
public abbrev surrogateEscape : CodecErrors := ⟨"surrogateescape"⟩

/--
For Unicode codecs, allow encoding and decoding a surrogate code point
({lit}`U+D800` - {lit}`U+DFFF`) as normal code point. Otherwise, these codecs
treat the presence of a lone surrogate as an error.
-/
public abbrev surrogatePass : CodecErrors := ⟨"surrogatepass"⟩

/--
When encoding text, replace unspported characters with XML/HTML numeric
character reference, which is a decimal form of Unicode code point with
format `&#num;`.
-/
public abbrev xmlCharRefReplace : CodecErrors := ⟨"xmlcharrefreplace"⟩

/--
When encoding text, replace unspported characters with {lit}`\N{...}`
escape sequences. What appears in the braces is the {lit}`Name` property
from the Unicode Character Database.
-/
public abbrev nameReplace : CodecErrors := ⟨"namereplace"⟩

end CodecErrors

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
