/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.CPtr
public import Nerodia.Data.Py.Basic
public import Nerodia.Control.PyIO.Basic
public import Nerodia.Control.MonadRaise

/-! # Low-level Python Monads -/

namespace Nerodia

/-! ## CPyResult -/

namespace Internal

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

end Internal

/-! ## C Monad Types -/

/--
Return context for external CPython functions that return an object
and may raise an exception.

Not a monad itself, but lifts into monads equipped with a Python context.
-/
@[expose] -- for codegen
public def CPyIO (α) :=
  BaseIO (Internal.CPyResult α)


namespace CPyIO

/-- Constructs a {lean}`CPyIO` function from its definition.  -/
@[inline] def ofBaseIOUnsafe (x : BaseIO (Internal.CPyResult α)) : CPyIO α :=
  x

/--
Runs the {lean}`CPyIO` function, returning the raw, unmanaged pointer.

**Safety**
* Users must ensure a Python context exists.
* Users must ensure the raised exception is handled on {name}`Internal.CPyResult.IsFailure`.
* **Memory:** Users must ensure that a returned object reference is consumed,
and that it does not outlive the enviroment.
-/
@[inline] def toBaseIOUnsafe (x : CPyIO α) : BaseIO (Internal.CPyResult α) :=
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
  BaseIO (Internal.CPyBaseResult α)

namespace CPyBaseIO

@[inline] def ofBaseIOUnsafe (x : BaseIO (Internal.CPyBaseResult α)) : CPyBaseIO α :=
  x

/--
Runs the {lean}`CPyBaseIO` function, returning the raw, unmanaged pointer.

**Safety**
* Users must ensure a Python context exists.
* **Memory:** Users must ensure that the returned object reference is consumed,
and that it  does not outlive the enviroment.
-/
@[inline] def toBaseIOUnsafe (x : CPyBaseIO α) : BaseIO (Internal.CPyBaseResult α) :=
  x

/-- Constructs a {lean}`CPyBaseIO` using the result of {lean}`x`. -/
@[inline] public def ofBind (x : BaseIO α) (f : α → CPyBaseIO β) : CPyBaseIO β :=
  ofBaseIOUnsafe do f (← x)

/-- Lifts a {lean}`CPyBaseIO` into a successful {lean}`CPyIO`. -/
@[inline] public def toCPyIO (x : CPyBaseIO α) : CPyIO α :=
  .ofBaseIOUnsafe <| x.toBaseIOUnsafe.map .ofCPyBaseResultUnsafe

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
opaque PyEnvironment.mkObjectUnsafe (env : @& PyEnvironment) (o : Internal.CPyBaseResult α) : α :=
  Classical.choice o.nonempty

@[extern "nerodia_mk_object", inherit_doc PyEnvironment.mkObjectUnsafe]
abbrev PyContext.mkObjectUnsafe (ctx : @& PyContext) (o : Internal.CPyBaseResult α) : α :=
  Classical.choice o.nonempty

@[inline, inherit_doc PyEnvironment.mkObjectUnsafe]
def ofBaseResultUnsafe
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m]
  (r : Internal.CPyBaseResult α)
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

  /--
Lifts the {lean}`CPyUnitIO` function into {lean}`PyIO`,
reusing its Python context.
-/
@[inline] public def toPyIO (x : CPyUnitIO) : PyIO Unit := do
  if (← x.runUnsafe) < 0 then
    .failureUnsafe

public instance : Coe CPyUnitIO (PyIO Unit) := ⟨toPyIO⟩

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

/-! ## PyResultIO -/

@[expose] -- for codegen
public def PyResultIO (α : Type) :=
  PyBaseIO (Internal.CPyResult α)

namespace PyResultIO

@[inline] def ofPyBaseIOUnsafe (x : PyBaseIO (Internal.CPyResult α)) : PyResultIO α :=
  x

@[inline] def toPyBaseIOUnsafe (x : PyResultIO α) : PyBaseIO (Internal.CPyResult α) :=
  x

@[inline] def runUnsafe (ctx : PyContext) (x : PyResultIO α) : BaseIO (Internal.CPyResult α) :=
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

/-! ## Exception Handling -/

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
@[inline] opaque PyContext.unsetException (ctx : PyContext) : PySystemError :=
  ctx.systemError! "no exception was set"

@[inline, inherit_doc PyContext.unsetException]
def getUnsetException  [Functor m] [MonadPy m] : m PyBaseException :=
  (·.unsetException) <$> getPyContextUnsafe

/-- Clears the current exception and returns it. -/
@[extern "nerodia_get_raised_exception"]
opaque getCRaisedException : CPyIO PyBaseException

/--
Clears the current exception and returns it.
If none, instead returns {name}`getUnsetException`.
-/
@[inline] def getRaisedException
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

/--
Sets the currently raised exception to {lean}`e`, stealing its reference.

**Safety**
* **Memory:** {lean}`e` must not be used after this call.
* **Correctness:** Must ensure the exception is handled or signaled.
-/
@[extern "nerodia_set_exception_result"]
opaque setExceptionResultUnsafe
  (e : Internal.CPyBaseResult PyBaseException) : BaseIO Unit

/-- Raises the error returned by {lean}`x`. -/
@[inline] public def Internal.raiseNew
  (x : CPyIO PyBaseException)
: CPyIO α := .ofBaseIOUnsafe do
  let e ← x.toBaseIOUnsafe
  if h : ¬ e.IsFailure then
    setExceptionResultUnsafe (e.toCPyBaseResultUnsafe h)
  return .failureUnsafe

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
