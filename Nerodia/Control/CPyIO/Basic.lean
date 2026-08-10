/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.CPtr
public import Nerodia.Data.Py.Basic
public import Nerodia.Data.Py.Raw.Basic
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
Converts the {name}`CPyBaseResult` to a raw Python object pointer,
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
Promotes a {name}`CPyResult` returning a typed Python object to one returning
its supertype, sharing the single strong reference between them.

**Memory Safety:** Users must manually manage the reference's lifetime.
-/
@[inline] def promote [IsSubtypeOf U T] (x : CPyResult (Py T)) : CPyResult (Py U) :=
  let cptr := .ofNullableAddrUnsafe x.toNullableCPtrUnsafe.nullableAddr fun h' =>
    let t := Classical.choice <| x.toNullableCPtrUnsafe.nonempty_of_not_isNull h'
    ⟨Py.mk t.raw (infer_subtype.hasType_of_hasType t.raw_hasType)⟩
  .ofNullableCPtrUnsafe cptr fun _ => inferInstance

/--
Casts a {name}`CPyResult` returning anything to one returning
an untyped object, sharing the single strong reference between them.

**Memory Safety:** Users must manually manage the reference's lifetime.
-/
@[inline] def raw (x : CPyResult α) : CPyResult Py.Raw :=
  let addr := x.toNullableCPtrUnsafe.nullableAddr
  let cptr := .ofNullableAddrUnsafe  addr fun _ => inferInstance
  .ofNullableCPtrUnsafe cptr fun _ => inferInstance

end CPyResult

end Internal

open Internal (PyThreadCtx CPyBaseResult CPyResult getPyThreadCtxUnsafe)

/-! ## C Monad Types -/

/-! ### CPyIO -/

/--
Return context for external CPython functions that return an object
and may raise an exception.

Not a monad itself, but lifts into monads equipped with a Python context.

**API Caveat:** The definition of {name}`CPyIO` is not part of Nerodia's
public API. Nevertheless, it is exposed due to the limitations of Lean's compiler.
-/
@[irreducible, expose] -- for codegen
public def CPyIO (α) :=
  BaseIO (CPyResult α)


namespace CPyIO

unseal CPyIO in
/-- Constructs a {lean}`CPyIO` function from its definition.  -/
@[inline] def ofBaseIOUnsafe (x : BaseIO (CPyResult α)) : CPyIO α :=
  x

unseal CPyIO in
/--
Runs the {lean}`CPyIO` function, returning the raw, unmanaged pointer.

**Safety**
* Users must ensure a Python context exists.
* Users must ensure the raised exception is handled on failure.
* **Memory:** Users must ensure that a returned object reference is consumed,
and that it does not outlive the environment.
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
  ofBaseIOUnsafe do f (← x) |>.toBaseIOUnsafe

set_option linter.unusedVariables.funArgs false in
/--
Promotes a {lean}`CPyIO` returning a
typed Python object to one returning its supertype.
-/
@[inline] public def promote [IsSubtypeOf U T] (x : CPyIO (Py T)) : CPyIO (Py U) :=
  ofBaseIOUnsafe <| x.toBaseIOUnsafe.map (·.promote)
/--
Converts a {lean}`CPyIO` returning a
arbitrary type to one returning {lean}`Py.Raw`.
-/
@[inline] public def raw (x : CPyIO α) : CPyIO Py.Raw :=
  ofBaseIOUnsafe <| x.toBaseIOUnsafe.map (·.raw)

end CPyIO

/-! ### CPyBaseIO -/

/--
Return context for external CPython functions that return an object
and cannot raise an exception.

Not a monad itself, but lifts into monads equipped with a Python context.

**API Caveat:** The definition of {name}`CPyBaseIO` is not part of Nerodia's
public API. Nevertheless, it is exposed due to the limitations of Lean's compiler.
-/
@[irreducible, expose] -- for codegen
public def CPyBaseIO (α) :=
  BaseIO (CPyBaseResult α)

namespace CPyBaseIO

unseal CPyBaseIO in
@[inline] def ofBaseIOUnsafe (x : BaseIO (CPyBaseResult α)) : CPyBaseIO α :=
  x

unseal CPyBaseIO in
/--
Runs the {lean}`CPyBaseIO` function, returning the raw, unmanaged pointer.

**Safety**
* Users must ensure a Python context exists.
* **Memory:** Users must ensure that the returned object reference is consumed,
and that it  does not outlive the environment.
-/
@[inline] def toBaseIOUnsafe (x : CPyBaseIO α) : BaseIO (CPyBaseResult α) :=
  x

/-- Constructs a {lean}`CPyBaseIO` using the result of {lean}`x`. -/
@[inline] public def ofBind (x : BaseIO α) (f : α → CPyBaseIO β) : CPyBaseIO β :=
  ofBaseIOUnsafe do f (← x) |>.toBaseIOUnsafe

/-- Lifts a {lean}`CPyBaseIO` action into a successful {lean}`CPyIO`. -/
@[inline] public def toCPyIO (x : CPyBaseIO α) : CPyIO α :=
  .ofBaseIOUnsafe <| x.toBaseIOUnsafe.map .ofCPyBaseResultUnsafe

public instance : MonadLift CPyBaseIO CPyIO := ⟨CPyBaseIO.toCPyIO⟩

end CPyBaseIO

/-! ### CPyUnitIO -/

/--
Return type for external CPython functions that may error but do not return
a Python object.

Not a monad itself, but lifts into monads equipped with a Python context.

**API Caveat:** The definition of {name}`CPyUnitIO` is not part of Nerodia's
public API. Nevertheless, it is exposed due to the limitations of Lean's compiler.
-/
@[irreducible, expose] -- for codegen
public def CPyUnitIO :=
  BaseIO Int32

namespace CPyUnitIO

unseal CPyUnitIO in
/--
Constructs a {lean}`CPyUnitIO` function from its definition.

**Safety:** Users should ensure that an exception is set on error.
-/
@[inline] def ofBaseIOUnsafe (x : BaseIO Int32) : CPyUnitIO :=
  x

unseal CPyUnitIO in
/--
Runs the {lean}`CPyUnitIO` function.

**Safety:** Users must ensure that a set exception is handled.
-/
@[inline] def toBaseIOUnsafe (x : CPyUnitIO) : BaseIO Int32 :=
  x

/-- Constructs a {lean}`CPyUnitIO` that succeeds. -/
@[inline] public def ok : CPyUnitIO :=
  ofBaseIOUnsafe <| pure 0

public instance : Nonempty CPyUnitIO := ⟨ok⟩

/--
Constructs a {lean}`CPyUnitIO` that fails.

**Safety:** Users should ensure that an exception is set.
-/
@[inline] def failureUnsafe : CPyUnitIO :=
  ofBaseIOUnsafe <| pure (-1)

/--
Runs {lean}`e` if {lean}`x` has set an exception.

**Safety:** {lean}`e` must handle the set exception (i.e., at least clear it).
-/
@[inline] def orElseUnsafe
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m]
  (x : CPyUnitIO) (e : m PUnit)
: m PUnit := do if (← x.toBaseIOUnsafe) < 0 then e

open Internal in
/--
Lifts the {lean}`CPyUnitIO` function into {lean}`PyIO`,
reusing its Python context.
-/
@[inline] public def toPyIO (x : CPyUnitIO) : PyIO Unit := do
  x.orElseUnsafe .failureUnsafe

end CPyUnitIO

public instance : Coe CPyUnitIO (PyIO Unit) := ⟨CPyUnitIO.toPyIO⟩

open Internal in
/--
Runs a {lean}`PyIO` action producing nothing in {lean}`CPyUnitIO`.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyIO.toCPyUnitIO (x : PyIO Unit) : CPyUnitIO := .ofBaseIOUnsafe do
  let ctx ← PyThreadCtx.getOrInit
  match ( ← x.runUnsafe? ctx) with
  | some _ => CPyUnitIO.ok.toBaseIOUnsafe
  | none => CPyUnitIO.failureUnsafe.toBaseIOUnsafe

/-! ### PyCResultIO -/

@[irreducible, expose] -- for codegen
public def PyCResultIO (α : Type) :=
  PyBaseIO (CPyResult α)

namespace PyCResultIO

unseal PyCResultIO in
@[inline] def ofPyBaseIOUnsafe (x : PyBaseIO (CPyResult α)) : PyCResultIO α :=
  x

unseal PyCResultIO in
@[inline] def toPyBaseIOUnsafe (x : PyCResultIO α) : PyBaseIO (CPyResult α) :=
  x

open Internal in
@[inline] def runUnsafe (ctx : PyThreadCtx) (x : PyCResultIO α) : BaseIO (CPyResult α) :=
  x.toPyBaseIOUnsafe.runUnsafe ctx

/--
Runs a {lean}`PyCResultIO` action producing a Python object in {lean}`CPyIO`.

This creates a new temporary Python context for the call.
-/
@[inline] public def toCPyIO (x : PyCResultIO α) : CPyIO α := .ofBaseIOUnsafe do
  x.runUnsafe (← PyThreadCtx.getOrInit)

/--
Converts a {lean}`PyCResultIO` returning an
arbitrary type to one returning {lean}`Py.Raw`.
-/
@[inline] public def raw (x : PyCResultIO α) : PyCResultIO Py.Raw :=
  .ofPyBaseIOUnsafe do return (← x.toPyBaseIOUnsafe).raw

end PyCResultIO

/-- Lifts a {lean}`CPyIO` action into {lean}`PyCResultIO`. -/
@[inline] public def CPyIO.toPyResultIO
  (x : CPyIO α)
: PyCResultIO α := .ofPyBaseIOUnsafe do
  let r ← x.toBaseIOUnsafe
  Runtime.hold (← getPyThreadCtxUnsafe)
  return r

/-- Sequences a {lean}`PyCResultIO` action after a {lean}`PyBaseIO` action. -/
@[inline] public def PyBaseIO.bindPyResultIO
  (x : PyBaseIO α) (f : α → PyCResultIO β)
: PyCResultIO β := .ofPyBaseIOUnsafe do f (← x) |>.toPyBaseIOUnsafe

open Internal in
/-- Sequences a {lean}`PyCResultIO` action after a {lean}`PyIO` action. -/
@[inline] public def PyIO.bindPyResultIO
  (x : PyIO α) (f : α → PyCResultIO β)
: PyCResultIO β := .ofPyBaseIOUnsafe do
  match ← x.toPyBaseIOUnsafe? with
  | some a => f a |>.toPyBaseIOUnsafe
  | none => return .failureUnsafe

/-- Internal function for {lit}`@[py_module_fn]` -/
@[inline] public def Internal.pyBind
  {α : Type} (x : PyIO α) (f : α → PyCResultIO Py.Raw)
: PyCResultIO Py.Raw := x.bindPyResultIO f

/-! ## Result Handling -/

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
abbrev Internal.PyThreadCtx.mkObjectUnsafe (ctx : @& PyThreadCtx) (o : CPyBaseResult α) : α :=
  Classical.choice o.nonempty

@[inline, inherit_doc PyEnvironment.mkObjectUnsafe]
def ofBaseResultUnsafe
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m]
  (r : CPyBaseResult α)
: m α := return (← getPyThreadCtxUnsafe).mkObjectUnsafe r

namespace CPyBaseIO

/-- Runs the {lean}`CPyBaseIO` function in a supporting monad. -/
@[inline] public def toM {m α}
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m] (x : CPyBaseIO α)
: m α := do ofBaseResultUnsafe (← x.toBaseIOUnsafe)

/-- Lifts a {lean}`CPyBaseIO` action into {lean}`PyBaseIO`. -/
@[inline] public def toPyBaseIO (x : CPyBaseIO α) : PyBaseIO α := do
  x.toM

public instance : MonadLift CPyBaseIO PyBaseIO := ⟨toPyBaseIO⟩

end CPyBaseIO

/--
Runs {lean}`e` if {lean}`x` has set an exception.

**Safety:** {lean}`e` must handle the set exception (i.e., at least clear it).
-/
@[inline] def CPyIO.orElseUnsafe
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m]
  (x : CPyIO α) (e : m α)
: m α := do
  let res ← x.toBaseIOUnsafe
  if h : res.IsFailure then
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

open Internal in
/--
Sequences a {lean}`CPyBaseIO` action after a {lean}`PyBaseIO` action.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyBaseIO.bindCPyBaseIO
  (x : PyBaseIO α) (f : α → CPyBaseIO β)
: CPyBaseIO β := .ofBaseIOUnsafe do
  let ctx ← PyThreadCtx.getOrInit
  f (← x.runUnsafe ctx) |>.toBaseIOUnsafe

/--
Runs a {lean}`PyBaseIO` action producing a Python object in {lean}`CPyBaseIO`.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyBaseIO.toCPyBaseIO (x : PyBaseIO (Py T)) : CPyBaseIO (Py T) :=
  x.bindCPyBaseIO CPyBaseIO.pure

open Internal in
/--
Sequences a {lean}`CPyIO` action after a {lean}`PyBaseIO` action.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyBaseIO.bindCPyIO
  (x : PyBaseIO α) (f : α → CPyIO β)
: CPyIO β := .ofBaseIOUnsafe do
  let ctx ← PyThreadCtx.getOrInit
  f (← x.runUnsafe ctx) |>.toBaseIOUnsafe

/-- Constructs a successful {lean}`CPyIO` that returns {lean}`o`. -/
@[inline] public protected def CPyIO.pure (o : Py T) : CPyIO (Py T) :=
  CPyBaseIO.pure o |>.toCPyIO

open Internal in
/--
Sequences a {lean}`CPyIO` action after a {lean}`PyIO` action.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyIO.bindCPyIO (x : PyIO α) (f : α → CPyIO β) : CPyIO β := .ofBaseIOUnsafe do
  let ctx ← PyThreadCtx.getOrInit
  match (← x.runUnsafe? ctx) with
  | some a => f a |>.toBaseIOUnsafe
  | none => CPyIO.failureUnsafe.toBaseIOUnsafe

/--
Runs a {lean}`PyIO` action producing a Python object in {lean}`CPyIO`.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyIO.toCPyIO (x : PyIO (Py T)) : CPyIO (Py T) :=
  x.bindCPyIO CPyIO.pure

open Internal in
/-- Constructs a {lean}`PyCResultIO` that returns {lean}`o`. -/
@[inline] public protected def PyCResultIO.pure (o : Py T) : PyCResultIO (Py T) :=
  .ofPyBaseIOUnsafe <| liftM (m := BaseIO) do
    /-
    Due to the unique requirements of `pure` and `newRef`,
    the context does not need to be held (e.g., via `Runtime.hold`).

    1. `newRef` does not require an attached thread state.
    2. `newRef` is atomic on free-threaded builds.
    3. `PyCResultIO` requires the GIL held on non-free-threaded builds.

    `PyCResultIO` actions only lift to `CPyIO`, which requires a context to be
    held throughout its duration (either a Nerodia one or Python's own through
    a method call). Therefore, the GIL is held when not free-threaded, and the
    environment is always held throughout.
    -/
    return .ofCPyBaseResultUnsafe (← o.newRef.toBaseIOUnsafe)

/-! ## Exception Handling -/

/-- Clears the current exception. Does nothing if there is none. -/
@[extern "nerodia_py_thread_ctx_clear_error"]
opaque Internal.PyThreadCtx.clearError (ctx : @& PyThreadCtx) : BaseIO Unit

@[inline, inherit_doc Internal.PyThreadCtx.clearError]
def clearError [Bind m] [MonadPy m] [MonadLiftT BaseIO m] : m PUnit :=
  getPyThreadCtxUnsafe >>= (·.clearError)

/--
Constructs a {lit}`SystemError` with the string {lean}`msg`.
Panics if the construction fails (e.g., due to lack of memory).
-/
@[extern "nerodia_py_thread_ctx_system_error"]
opaque Internal.PyThreadCtx.systemError!
  (msg : @& String) (ctx : @& PyThreadCtx) : PySystemError

/-- The exception used when no other exception is set. -/
@[inline] opaque Internal.PyThreadCtx.unsetException (ctx : PyThreadCtx) : PySystemError :=
  ctx.systemError! "no exception was set"

@[inline, inherit_doc Internal.PyThreadCtx.unsetException]
def getUnsetException  [Functor m] [MonadPy m] : m PyBaseException :=
  (·.unsetException) <$> getPyThreadCtxUnsafe

/-- Clears the current exception and returns it. -/
@[extern "nerodia_get_raised_exception"]
opaque getCRaisedException : CPyIO PyBaseException

/--
Clears the current exception and returns it.
If none, instead returns {name}`getUnsetException`.
-/
@[inline] def getRaisedException
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m]
: m PyBaseException := getCRaisedException.orElseUnsafe getUnsetException

open Internal Nerodia in
/-- Returns the currently raised exception or {name}`unsetException` if none. -/
@[inline] protected def Internal.PyThreadCtx.getRaisedException
  (ctx : PyThreadCtx)
: BaseIO PyBaseException := PyBaseIO.runUnsafe ctx getRaisedException

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
  (e : CPyBaseResult PyBaseException) : BaseIO Unit

/-- Raises the error returned by {lean}`x`. -/
@[inline] public def Internal.raiseNew
  (x : CPyIO PyBaseException)
: CPyIO α := .ofBaseIOUnsafe do
  let e ← x.toBaseIOUnsafe
  if h : ¬ e.IsFailure then
    setExceptionResultUnsafe (e.toCPyBaseResultUnsafe h)
  return .failureUnsafe

namespace PyIO

open Internal in
/-- Raises the exception {lean}`e`. -/
@[inline] public protected def raise (e : PyBaseException) : PyIO α := do
  setRaisedExceptionUnsafe e
  .failureUnsafe

public instance : MonadRaise PyIO := ⟨PyIO.raise⟩

public instance : Inhabited (PyIO α) :=
  ⟨private_decl% getUnsetException >>= raise⟩

open Internal in
/--
Runs the {name}`PyIO` action {name}`x`.
If {name}`x` raises an exception {given}`e`, catches it and runs {lean}`f e`.
Exceptions in {name}`f` are not caught.
-/
@[inline] public def tryCatchM
  [Monad m] [MonadLiftT BaseIO m] [MonadPy m]
  (x : PyIO α) (f : PyBaseException → m α)
: m α := do
  let ctx ← getPyThreadCtxUnsafe
  (← x.runUnsafe? ctx).getDM do
    f (← ctx.getRaisedException)

public instance : MonadExceptOf PyBaseException PyIO where
  throw := PyIO.raise
  tryCatch := PyIO.tryCatchM

/--
Runs the {lean}`PyIO` function in {lean}`EIO`.

This creates a new temporary Python context for the call.
As such, it should only be used when another Python context is not available.
Otherwise, lift {lean}`x` into a supporting monad.
-/
@[inline] public def toEIO (x : PyIO α) : EIO PyBaseException α := do
  PyThreadCtxT.run' <| x.tryCatchM throw

open Internal in
/--
Runs the {name}`PyIO` action {name}`x`,
ensuring some other action always happens afterwards.

If {name}`x` raises an exception, catches it, runs {lean}`f none`, and then
re-raises the exception. Otherwise, if {name}`x` succeeds and returns
{given}`a : α`, runs {lean}`f (some a)`.
-/
@[inline] public protected def tryFinallyM'
  [Monad m] [MonadLiftT BaseIO m] [MonadPy m] [MonadRaise m]
  (x : PyIO α) (f : Option α → m β)
: m (α × β) := do
  let ctx ← getPyThreadCtxUnsafe
  if let some a ← x.runUnsafe? ctx then
    let b ← f (some a)
    return (a, b)
  else
    -- TODO: Should this set `e` as the handled exception for Python?
    let e ← getRaisedException
    let _ ← f none
    raise e

public instance : MonadFinally PyIO := ⟨PyIO.tryFinallyM'⟩

open Internal in
/--
Runs the {name}`PyIO` action {name}`x`.
If {name}`x` raises an exception, clears it and runs {lean}`f ()`.
-/
@[inline] public protected def orElseM
  [Monad m] [MonadLiftT BaseIO m] [MonadPy m]
  (x : PyIO α) (f : Unit → m α)
: m α := do
  let ctx ← getPyThreadCtxUnsafe
  (← x.runUnsafe? ctx).getDM do
    clearError
    f ()

public instance : OrElse (PyIO α) := ⟨PyIO.orElseM⟩

end PyIO

namespace CPyIO

/--
Runs the {lean}`CPyIO` function in a supporting monad.
If a Python error occurs, it is raised via {name}`throw`.
-/
@[inline] public def toM {m α}
  [Monad m] [MonadPy m]
  [MonadExcept PyBaseException m] [MonadLiftT BaseIO m]
  (x : CPyIO α)
: m α := x.orElseUnsafe do throw (← getRaisedException)

/--
Runs the {lean}`CPyIO` function in a supporting monad.
If a Python error occurs, it is set as the exception.
-/
@[inline] public def toExceptT
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m] (x : CPyIO α)
: ExceptT PyBaseException m α := x.toM

open Internal in
/-- Lifts the {lean}`CPyIO` function into {lean}`PyIO`, reusing its Python context. -/
@[inline] public def toPyIO (x : CPyIO α) : PyIO α :=
  x.orElseUnsafe .failureUnsafe

public instance : MonadLift CPyIO PyIO := ⟨toPyIO⟩

/--
Runs the {lean}`CPyIO` function in {lean}`EIO`.

This creates a new temporary Python context for the call.
As such, it should only be used when a Python context is not available.
Otherwise, run {lean}`x` via {name}`toM` or lift it into {lean}`PyIO`
(via {lean}`toPyIO`) and run it from there.
-/
@[inline] public def toEIO (x : CPyIO α) : EIO PyBaseException α :=
  x.toPyIO.toEIO

/--
Runs the {lean}`CPyIO` function in a supporting monad.
If a Python error occurs, it is cleared and {name}`failure` is called.
-/
@[inline] public def toAlternative
  [Monad m] [MonadPy m]
  [Alternative m] [MonadLiftT BaseIO m]
  (x : CPyIO α)
: m α := x.orElseUnsafe do
  clearError
  failure

/--
Runs the {lean}`CPyIO` function in a supporting monad
If a Python error occurs, it is cleared and {lean}`none` is set.
-/
@[inline] public def toOptionT
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m] (x : CPyIO α)
: OptionT m α := x.toAlternative

/--
Runs the {lean}`CPyIO` function in a supporting monad.
If a Python error occurs, it is cleared and {lean}`none` is returned.
-/
@[inline] public def toM?
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m] (x : CPyIO α)
: m (Option α) := x.toOptionT.run

/-- Raises the exception {lean}`e`.  -/
@[inline] public protected def raise
  (e : PyBaseException)
: CPyIO α := .ofBaseIOUnsafe do
  setRaisedExceptionUnsafe e
  CPyIO.failureUnsafe.toBaseIOUnsafe

public instance : MonadRaise CPyIO := ⟨CPyIO.raise⟩

@[inline] public protected def tryCatchM
  [Monad m] [MonadLiftT BaseIO m] [MonadPy m]
  (x : CPyIO α) (f : PyBaseException → m α)
: m α := x.orElseUnsafe do f (← getRaisedException)

end CPyIO

namespace CPyUnitIO

/--
Runs the {lean}`CPyUnitIO` function in a supporting monad.
If a Python error occurs, it is raised via {name}`throw`.
-/
@[inline] public def toM
  [Monad m] [MonadPy m]
  [MonadExcept PyBaseException m] [MonadLiftT BaseIO m]
  (x : CPyUnitIO)
: m PUnit := x.orElseUnsafe do throw (← getRaisedException)

/--
Runs the {lean}`CPyUnitIO` function in a supporting monad.
If a Python error occurs, it is set as the exception.
-/
@[inline] public def toExceptT
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m] (x : CPyUnitIO)
: ExceptT PyBaseException m PUnit := x.toM

/--
Runs the {lean}`CPyUnitIO` function in {lean}`EIO`.

This creates a new temporary Python context for the call.
As such, it should only be used when a Python context is not available.
Otherwise, run {lean}`x` via {name}`toM` or lift it into {lean}`PyIO`
(via {lean}`toPyIO`) and run it from there.
-/
@[inline] public def toEIO (x : CPyUnitIO) : EIO PyBaseException Unit :=
  x.toPyIO.toEIO

/--
Runs the {lean}`CPyUnitIO` function in a supporting monad.
If a Python error occurs, it is cleared and {name}`failure` is called.
-/
@[inline] public def toAlternative
  [Monad m] [MonadPy m]
  [Alternative m] [MonadLiftT BaseIO m]
  (x : CPyUnitIO)
: m PUnit := x.orElseUnsafe do clearError; failure

end CPyUnitIO
