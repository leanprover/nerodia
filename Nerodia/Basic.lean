/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

/-! # Nerodia -/

namespace Nerodia

/-! ## CPtr -/

/--
A raw pointer to a Python object.

This pointer is not managed by Lean and must instead be managed by the user.
-/
public structure CPtr (α : Type u) : Type where
  private innerMk ::
    addr : USize
    private nonempty_of_addr_ne_zero : addr ≠ 0 → Nonempty α

namespace CPtr

public theorem addr_inj : addr a = addr b ↔ a = b := by
  cases a; cases b; simp

@[inline] public def decEq (a b : CPtr α) : Decidable (a = b) :=
  let ⟨a, _⟩ := a
  let ⟨b, _⟩ := b
  if h : a = b then
    isTrue (addr_inj.mp h)
  else
    isFalse (addr_inj.subst h)

@[inline] instance : DecidableEq (CPtr α) := decEq

@[inline] public def null : CPtr α :=
  ⟨0, by simp⟩ -- `NULL = 0` on Lean-supported platforms

instance : Inhabited (CPtr α) := ⟨null⟩

public abbrev IsNull (self : CPtr α) : Prop :=
  self = null

public theorem nonempty_of_not_isNull
  {p : CPtr α} (h : ¬ IsNull p) : Nonempty α
:= p.nonempty_of_addr_ne_zero <| by simpa [← addr_inj, null] using h

/--
Casts a pointer of type {lean}`α` to a pointer of type {lean}`β`.

**This function is not memeory-safe.** While {lean}`f` demonstrates that
{lean}`α` can be converted into {lean}`β`, it does not prove they have same
memory layout. It is the user's responsibility to ensure this.
-/
@[inline] public def castUnsafe  (f : α → β) (p : CPtr α) : CPtr β :=
  ⟨p.addr, fun h => p.nonempty_of_addr_ne_zero h |>.elim fun a => .intro <| f a⟩

end CPtr

/-! ## PyContext -/

private opaque PyContext.nonemptyType : NonemptyType.{0}

/--
Reference holder for the Python environment.
When this object is freed, Python will be uninitialized.

Python objects created by Nerodia implicitly hold a reference to the context,
so the context will not be freed until all Python objects managed by Lean
are freed.
-/
public def PyContext := PyContext.nonemptyType.type

namespace PyContext

public instance : Nonempty PyContext := PyContext.nonemptyType.property

/--
Returns a reference to the Python environment.

If no Python environment exists yet, it will be initialized.
Otherwise, this function acquires the Python global interpreter lock (GIL).
-/
@[extern "nerodia_py_context_init"]
public opaque init : BaseIO PyContext

/-- Wraps a strong Python object refernce into a memory-managed Lean object. -/
@[extern "nerodia_py_context_mk_object"]
public opaque mkObject {α} (ctx : @& PyContext) (ptr : CPtr α) (h : ¬ ptr.IsNull) : α :=
  @Classical.ofNonempty (α := α) (ptr.nonempty_of_not_isNull h)

/-- Wraps a borrowed Python object referemce into a memory-managed Lean object. -/
@[extern "nerodia_py_context_mk_object_ref"]
public opaque mkObjectRef {α} (ctx : @& PyContext) (ptr : CPtr α) (h : ¬ ptr.IsNull) : α :=
  @Classical.ofNonempty (α := α) (ptr.nonempty_of_not_isNull h)

/-- Clears the current exception. Does nothing if there is none. -/
@[extern "nerodia_py_context_clear_error"]
public opaque clearError (ctx : @& PyContext) : BaseIO Unit

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
public opaque addr (self : @& PyObject) : USize

/--
Returns a borrowed reference to Python object's raw unmanaged C pointer.

**This function is not memory safe.** It is the user's responsibility to
ensure that this pointer does not outlive {lean}`self`.
-/
@[inline] def borrowRefUnsafe (self : @& PyObject) : CPtr PyObject :=
  ⟨self.addr, fun _ => ⟨self⟩⟩

/--
Returns a new strong reference to Python object's raw unmanaged C pointer.

**This function is not memory safe.** It is the user's responsibility to
ensure that this reference is eventually consumed.
-/
@[extern "nerodia_py_object_new_ref"]
def newRefUnsafe (self : @& PyObject) : CPtr PyObject :=
  ⟨self.addr, fun _ => ⟨self⟩⟩

/-- Returns a reference to the Python environment this object is within. -/
@[extern "nerodia_py_object_ctx"]
public opaque ctx (self : @& PyObject) : PyContext

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
public structure PyType extends toObject : PyObject where
  private innerMk ::
    deriving Nonempty

/-- A Python base exception object. That is, an instance of {lit}`BaseException`. -/
public structure PyBaseException extends toObject : PyObject where
  private innerMk ::
    deriving Nonempty

/-- A Python exception object. That is, an instance of {lit}`Exception`. -/
public structure PyException extends toBaseException : PyBaseException where
  private innerMk ::
    deriving Nonempty

public instance : Coe PyException PyBaseException :=
  ⟨PyException.toBaseException⟩

/-- A Python system error object. That is, an instance of {lit}`SystemError`. -/
public structure PySystemError extends toException : PyException where
  private innerMk ::
    deriving Nonempty

public instance : Coe PySystemError PyException :=
  ⟨PySystemError.toException⟩

/-- A Python type error object. That is, an instance of {lit}`TypeError`. -/
public structure PyTypeError extends toException : PyException where
  private innerMk ::
    deriving Nonempty

public instance : Coe PyTypeError PyException :=
  ⟨PyTypeError.toException⟩

/-- A Python module object. That is, an instance of {lit}`types.ModuleType`. -/
public structure PyModule extends toObject : PyObject where
  private innerMk ::
    deriving Nonempty

/-- A Python unicode object. That is, an instance of {lit}`str`. -/
public structure PyStr extends toObject : PyObject where
  private innerMk ::
    deriving Nonempty

public instance : Coe PyStr PyObject := ⟨PyStr.toObject⟩

set_option linter.unusedVariables.funArgs false in
@[inline] public def PyStr.mk (o : PyObject) (h : o.isStrInstance) : PyStr :=
  ⟨o⟩

/-- A Python bytes object. That is, an instance of {lit}`bytes`. -/
public structure PyBytes extends toObject : PyObject where
  private innerMk ::
    deriving Nonempty

/-! ## Builtin Objects -/

namespace PyContext

/-! ### Constants -/

@[extern "nerodia_py_context_none"]
public opaque none (ctx : @& PyContext) : PyObject

/-! ### Type Objects -/

/-- Returns a reference to the type of types (i.e., {lit}`type` in Python). -/
@[extern "nerodia_py_context_type_type"]
public opaque typeType (ctx : @& PyContext) : PyType

/-- Returns a reference to the unicode string type (i.e., {lit}`str` in Python). -/
@[extern "nerodia_py_context_str_type"]
public opaque strType (ctx : @& PyContext) : PyType

end PyContext

/-! ## Monad -/

/-- Type class of monads equipped with a Python environment. -/
public class MonadPy (m : Type → Type u) where
  getPyContext : m PyContext

export MonadPy (getPyContext)

public instance [MonadLift m n] [MonadPy m] :MonadPy n where
  getPyContext := liftM (m := m) getPyContext

@[inline, inherit_doc PyContext.clearError]
public def clearError [Bind m] [MonadPy m] [MonadLiftT BaseIO m] : m PUnit :=
  getPyContext >>= (·.clearError)

/-- A monad transformer to equip a monad with a Python environment. -/
public abbrev PyT := ReaderT PyContext

namespace PyT
public instance [Monad m] : MonadPy (PyT m) := ⟨read⟩
end PyT

/-- The primary monad for impure code using Python. -/
@[expose] -- for codegen
public def PyIO (α) := PyT BaseIO (Option α)

namespace PyIO

@[inline] def mk (x : PyT (OptionT BaseIO) α) : PyIO α :=
  x

/--
Runs the {lean}`PyIO` function, returning {lean}`none` if an exception was raised.

This function is conceptually unsafe because it does not necessarily handle
the raised exception.
-/
@[inline] def runUnsafe? (ctx : PyContext) (x : PyIO α) : BaseIO (Option α) :=
  x ctx

/--
Constructs a {lean}`PyIO` that fails.

This function is conceptually unsafe because it does not guarantee
that an exception is set on error.
-/
@[inline] def failureUnsafe : PyIO α :=
  mk <| failure

@[inline] public protected def pure (a : α) : PyIO α :=
  mk <| pure a

public instance : Pure PyIO := ⟨PyIO.pure⟩

@[inline] public protected def map (f : α → β) (x : PyIO α) : PyIO β :=
  mk <| Functor.map f x

public instance : Functor PyIO where map := PyIO.map

@[inline] public protected def bind (x : PyIO α) (f : α → PyIO β) : PyIO β :=
  mk <| bind x f

-- used by @[py_module_fn]
public instance instBind : Bind PyIO := ⟨PyIO.bind⟩

public instance : Monad PyIO := {}

end PyIO

/-- A monad for impure code using Python. Unlike {lean}`PyIO`, it cannot error. -/
public abbrev PyBaseIO := PyT BaseIO

namespace PyBaseIO

@[inline] public def toPyIO (x : PyBaseIO α) : PyIO α := fun ctx =>
  x.run ctx

public instance : MonadLift PyBaseIO PyIO := ⟨toPyIO⟩

@[inline] public nonrec def toBaseIO (x : PyBaseIO α) : BaseIO α := do
  x.run (← PyContext.init)

public instance : MonadEval PyBaseIO BaseIO := ⟨PyBaseIO.toBaseIO⟩

end PyBaseIO

/--
Return context for external CPython functions.

Not a monad itself, but lifts into monads equipped with a Python environment.
-/
@[expose] -- for codegen
public def CPyIO (α) :=
  BaseIO (CPtr α)

namespace CPyIO

/-- Constructs a {lean}`CPyIO` function from its definition.  -/
@[inline] public def mkUnsafe (x : BaseIO (CPtr α)) : CPyIO α :=
  x

public instance : Nonempty (CPyIO α) := ⟨mkUnsafe <| pure .null⟩

/--
Runs the {lean}`CPyIO` function, returning the raw, unmanaged pointer.

**This function is not memory safe.** It is the user's responsibility to ensure
that a Python environment exists and the returned pointer does not outlive it.
-/
@[inline] def runUnsafe (x : CPyIO α) : BaseIO (CPtr α) :=
  x

/--
Constructs a {lean}`CPyIO` that fails.

This function is conceptually unsafe because it does not guarantee
that an exception is set on error.
-/
@[inline] def failureUnsafe : CPyIO α :=
  mkUnsafe <| pure .null

/-- Converts a {lean}`CPyIO` returning a typed Python object into untyped general object. -/
@[inline] public def cast (x : CPyIO α) : CPyIO PyObject :=
  unsafe unsafeCast x

end CPyIO

/--
Runs a {lean}`PyIO` action producing a Python object in {lean}`CPyIO`.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyIO.toCPyIO (x : PyIO PyObject) : CPyIO PyObject := .mkUnsafe do
  let ctx ← PyContext.init
  match ( ← x.runUnsafe? ctx) with
  | some obj => return obj.newRefUnsafe
  | none => CPyIO.failureUnsafe

/--
Sequences a {lean}`CPyIO` action after a {lean}`PyIO` action.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyIO.bindC (x : PyIO α) (f : α → CPyIO β) : CPyIO β := .mkUnsafe do
  let ctx ← PyContext.init
  match (← x.runUnsafe? ctx) with
  | some a => f a
  | none => CPyIO.failureUnsafe

/-- Clears the current exception and returns it. -/
@[extern "nerodia_get_raised_exception"]
private opaque getRaisedException : CPyIO PyBaseException

/--
Constructs a {lit}`SystemError` with the string {lean}`msg`.
Panics if the construction fails (e.g., due to lack of memeory).
-/
@[extern "nerodia_py_context_system_error"]
opaque PyContext.systemError! (msg : @& String) (ctx : @& PyContext) : PySystemError

/-- The exception used when when no other exception is set. -/
@[inline] public def PyContext.unsetException (ctx : PyContext) : PySystemError :=
  ctx.systemError! "no exception was set"

/-- Returns the currently raised exception or {name}`unsetException` if none. -/
@[inline] public protected def PyContext.getRaisedException
  (ctx : PyContext)
: BaseIO PyBaseException := do
  let eptr ← getRaisedException.runUnsafe
  if h : eptr.IsNull then
    return ctx.unsetException
  else
    return ctx.mkObject eptr h

/--
Runs the {lean}`PyIO` function in {lean}`EIO`.

This creates a new temporary Python context for the call.
As such, it should only be used when another Python context is not available.
Otherwise, use {lean}`x.run` and provider the context or lift {lean}`x` into
a supporting monad.
-/
@[inline] public def PyIO.toEIO (x : PyIO α) : EIO PyBaseException α := do
  let ctx ← PyContext.init
  match (← x.runUnsafe? ctx) with
  | some a => return a
  | none => throw (← ctx.getRaisedException)

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
  let ctx ← getPyContext
  let ptr ← x.runUnsafe
  if h : ptr.IsNull then
    throw (← ctx.getRaisedException)
  else
    return ctx.mkObject ptr h

/--
Runs the {lean}`CPyIO` function in a supporting monad
If a Python error occurs, it is set as the exception.
-/
public abbrev toExceptT
  [Monad m] [MonadPy m] [MonadLiftT BaseIO m] (x : CPyIO α)
: ExceptT PyBaseException m α := x.run

/-- Lifts the {lean}`CPyIO` function into {lean}`PyIO`, reusing its Python context. -/
@[inline] public def toPyIO (x : CPyIO α) : PyIO α := do
  let ctx ← getPyContext
  let ptr ← x.runUnsafe
  if h : ptr.IsNull then
    .failureUnsafe
  else
    return ctx.mkObject ptr h

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
  let ctx ← getPyContext
  let ptr ← x.runUnsafe
  if h : ptr.IsNull then
    ctx.clearError
    failure
  else
    return ctx.mkObject ptr h

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

end CPyIO

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

This function is unsafe because it does not guarantee that an exception
is set on error.
-/
@[inline] def mkUnsafe (x : BaseIO Int32) : CPyUnitIO :=
  x

/--
Runs the {lean}`CPyUnitIO` function.

This function is unsafe because it does not guarantee that a set exception
is handled and thus ensure Python's correctness [requirement][1] that futher
Python functions are not called while an exception is set.

[1]: https://bugs.python.org/issue23571
-/
@[inline] def runUnsafe (x : CPyUnitIO) : BaseIO Int32 :=
  x

/-- Constructs a {lean}`CPyUnitIO` that succeeds. -/
@[inline] public def ok : CPyUnitIO :=
  mkUnsafe <| pure 0

public instance : Nonempty CPyUnitIO := ⟨ok⟩

/--
Constructs a {lean}`CPyUnitIO` that fails.

This function is conceptually unsafe because it does not guarantee
that an exception is set on error.
-/
@[inline] def failureUnsafe : CPyUnitIO :=
  mkUnsafe <| pure (-1)

/--
Runs the {lean}`CPyIO` function in a supporting monad.
If a Python error occurs, it is raised via {name}`throw`.
-/
@[inline] public def run
  [Monad m] [MonadPy m]
  [MonadExcept PyBaseException m] [MonadLiftT BaseIO m]
  (x : CPyUnitIO)
: m PUnit := do
  let ctx ← getPyContext
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
  let ctx ← getPyContext
  if (← x.runUnsafe) < 0 then
    ctx.clearError
    failure

end CPyUnitIO

/--
Runs a {lean}`PyIO` action producing nothing in {lean}`CPyUnitIO`.

This creates a new temporary Python context for the call.
-/
@[inline] public def PyIO.toCPyUnitIO (x : PyIO Unit) : CPyUnitIO := .mkUnsafe do
  let ctx ← PyContext.init
  match ( ← x.runUnsafe? ctx) with
  | some _ => CPyUnitIO.ok
  | none => CPyUnitIO.failureUnsafe

/--
Sets the currently raised exception to {lean}`e`.
If {lean}`e.IsNull`, this just clears the exception.

**This function is not memory-safe.** It is the user's responsibility to
ensure that {lean}`e` is still alive (if it is not {lean}`CPtr.null`). This
will usually be the case unless it came from a different Python environment.
-/
@[extern "nerodia_set_raised_exception"]
opaque setRaisedExceptionUnsafe (e : CPtr PyBaseException) : BaseIO Unit

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
public def raise [MonadRaise m] [ToBaseException ε] (e : ε) : m α :=
  MonadRaise.raise (ToBaseException.toBaseException e)

namespace CPyIO

/--
Clears any current exception and raises {lean}`e`.
If {lean}`e.IsNull`, just clears the exception.

**This function is memory unsafe.**  It is the user's responsibility to
ensure that {lean}`e` is still alive (if it is not {lean}`CPtr.null`).
-/
@[inline] def raiseUnsafe (e : CPtr PyBaseException) : CPyIO α := .mkUnsafe do
  setRaisedExceptionUnsafe e
  CPyIO.failureUnsafe

/-- Raises the exception {lean}`e`.  -/
@[inline] public protected def raise (e : PyBaseException) : CPyIO α := .mkUnsafe do
  raiseUnsafe (e.newRefUnsafe.castUnsafe (⟨·⟩))

public instance : MonadRaise CPyIO := ⟨CPyIO.raise⟩

@[inline] public protected def tryCatch
  [Monad m] [MonadLiftT BaseIO m] [MonadPy m]
  (x : CPyIO α) (f : PyBaseException → m α)
: m α := do
  let ctx ← getPyContext
  let ptr ← x.runUnsafe
  if h : ptr.IsNull then
    f (← ctx.getRaisedException)
  else
    return ctx.mkObject ptr h

end CPyIO

namespace PyIO

/-- Raises the exception {lean}`e`. -/
@[inline] public protected def raise (e : PyBaseException) : PyIO α := do
  setRaisedExceptionUnsafe (e.newRefUnsafe.castUnsafe (⟨·⟩))
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
  let ctx ← getPyContext
  match (← x.runUnsafe? ctx) with
  | some a => return a
  | none => f (← ctx.getRaisedException)

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
  let ctx ← getPyContext
  if let some a ← x.runUnsafe? ctx then
    let b ← f (some a)
    return (a, b)
  else
    let e ← ctx.getRaisedException
    let _ ← f none
    raise e

public instance : MonadFinally PyIO where
  tryFinally' := PyIO.tryFinally'

/--
Runs the {name}`PyIO` action {name}`x`.
If {name}`x` raises an exception, clears it and runs {lean}`f ()`.
-/
@[inline] public protected def orElse
  [Monad m] [MonadLiftT BaseIO m] [MonadPy m]
  (x : PyIO α) (f : Unit → m α)
: m α := do
  let ctx ← getPyContext
  if let some a ← x.runUnsafe? ctx then
    return a
  else
    ctx.clearError
    f ()

end PyIO

/-- A raw C object pointer provided as a Python function argument. -/
public structure TCPyArg (α : Type u) where
  private mk ::
    private ptr : CPtr α
    private not_isNull_ptr : ¬ ptr.IsNull

/-- A raw C object pointer provided as a Python function argument. -/
public abbrev CPyArg := TCPyArg PyObject

@[inline] def PyContext.mkArgUnsafe (ctx : PyContext) (arg : TCPyArg α) : α :=
  ctx.mkObjectRef arg.ptr arg.not_isNull_ptr

/-- The type of a Python method with no arguments. -/
@[expose] -- for codegen
public def PyMethNoArgs :=
  (self : CPyArg) → (arg : CPtr PyObject) →
  (h_arg : arg.IsNull) → CPyIO PyObject

@[inline] public def PyMethNoArgs.ofPyIO
  (x : (self : PyObject) → PyIO PyObject)
: PyMethNoArgs := fun self _ _ => PyIO.toCPyIO do
  let ctx ← getPyContext
  let self := ctx.mkArgUnsafe self
  x self

@[inline] public def PyMethNoArgs.ofPyIO'
  (x : PyIO PyObject)
: PyMethNoArgs := ofPyIO fun _ => x

@[inline] public def PyMethNoArgs.ofCPyIO
  (x : CPyIO PyObject)
: PyMethNoArgs := fun _ _ _ => x

/-- A raw C array of Python function arguments. -/
public structure CPyArgs where
  private mk ::
    private addr : USize

@[extern "nerodia_py_context_mk_args"]
opaque PyContext.mkArgsUnsafe (ctx : @& PyContext) (args : CPyArgs) (nargs : USize) : Array PyObject

@[extern "nerodia_py_context_mk_nth_arg"]
opaque PyContext.mkNthArgUnsafe (ctx : @& PyContext) (args : CPyArgs) (i : USize) : PyObject

/-- The type of a Python method with a single positional argument. -/
@[expose] -- for codegen
public def PyMethFastCall :=
  (self : CPyArg) → (args : CPyArgs) → (nargs : USize) → CPyIO PyObject

@[inline] public def PyMethFastCall.ofPyIO
  (x : (self : PyObject) → (args : Array PyObject) → PyIO PyObject)
: PyMethFastCall := fun self args nargs => PyIO.toCPyIO do
  let ctx ← getPyContext
  let self := ctx.mkArgUnsafe self
  let args := ctx.mkArgsUnsafe args nargs
  x self args

/-- **Do not use.** Internal function for {lit}`@[py_module_fn]`. -/
@[inline] public def PyMethFastCall.mkInternalUnsafe
  (x : (args : CPyArgs) → (nargs : USize) → PyIO PyObject)
: PyMethFastCall := fun _ args nargs =>  x args nargs |>.toCPyIO

/-- The type of a Python method with a single positional argument. -/
@[expose] -- for codegen
public def PyMethO :=
  (self : CPyArg) → (arg : CPyArg) → CPyIO PyObject

@[inline] public def PyMethO.ofPyIO
  (x : (self : PyObject) → (arg : PyObject) → PyIO PyObject)
: PyMethO := fun self arg => PyIO.toCPyIO do
  let ctx ← getPyContext
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
  let ctx ← getPyContext
  x (ctx.mkArgUnsafe mod)

@[extern "nerodia_set_py_type_error"]
opaque setPyTypeErrorUnsafe (msg : @& String) : BaseIO Unit

/-- Raises a {lean}`PyTypeError` with the given message {lean}`msg`. -/
@[inline] public def raisePyTypeError (msg : String) : CPyIO α := .mkUnsafe do
  setPyTypeErrorUnsafe msg
  return .null

/-- Raises a {lean}`PyTypeError` indicating {lit}`fn` was called with the wrong number of arguments. -/
@[inline] public def raiseArityNotEq (fn : String) (expected given : USize) : CPyIO α := do
  raisePyTypeError s!"{fn} takes exactly {expected} arguments ({given} given)"

/-! ## PyType -/

namespace PyType


public instance : Coe PyType PyObject := ⟨toObject⟩

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
@[extern "nerodia_py_object_type"]
public opaque PyObject.type (self : @& PyObject) : PyType

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
@[inline] public def ofPyArgUnsafe
  [OfPyArg α ty] (fn : String) (i : USize) (args : CPyArgs) : PyIO α
:= do OfPyArg.ofPyArg fn (i.toNat+1) ((← getPyContext).mkNthArgUnsafe args i)

/--
Type class used to construct Python attributes from Lean objects.
Used by {lit}`@[py_module_attr]`.
-/
public class MkAttr (α : Type u) (ty : outParam String) where
  mkAttr : α → CPyIO PyObject

public instance : MkAttr PUnit "None" where
  mkAttr _ := private .mkUnsafe <| return (← PyContext.init).none.newRefUnsafe

public instance [MkAttr α ty] : MkAttr (BaseIO α) ty where
  mkAttr x := private .mkUnsafe do MkAttr.mkAttr (← x)

public instance [MkAttr α ty] : MkAttr (PyIO α) ty where
  mkAttr x := x.bindC MkAttr.mkAttr

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

public instance : MkAttr String "str" := ⟨(mkPyStr · |>.cast)⟩

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

/-- Returns the UTF8-encoded value of {lean}`self` as a Lean {lean}`String`. -/
-- This function is pure because the string data of instances of `str` is immutable.
@[extern "nerodia_py_str_to_string"]
public opaque PyStr.toString (self : @& PyStr) : String

public instance : ToString PyStr := ⟨PyStr.toString⟩

public instance : OfPyArg String "str" where
  ofPyArg fn i o :=
    if h : o.isStrInstance then
      return (PyStr.mk o h).toString
    else raisePyTypeError s!"{fn} argument {i} must be str"

/-- Returns the UTF8-encoded value of the Python string as Python bytes. -/
@[extern "nerodia_py_str_utf8_encode"]
public opaque PyStr.utf8Encode (self : @& PyStr) : CPyIO PyBytes

/-- Returns the bytes of {lean}`self` as a Lean {lean}`ByteArray`. -/
-- This function is pure because the bytes data of instances of `bytes` is immutable.
@[extern "nerodia_py_bytes_to_byte_array"]
public opaque PyBytes.toByteArray (self : @& PyBytes) : ByteArray

/-! ## Exception Handling -/

namespace PyIO

/--
Runs the {lean}`PyIO` function in {lean}`IO`.

Python errors will be formatted in the standard Python convention and
reported as {lean}`IO.userError`.

This creates a new temporary Python context for the call.
As such, it should only be used when a Python context is not available.
For example, this can be used in {lit}`main` to run a {lean}`PyIO` function.
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
  let ctx ← PyContext.init
  if let some a ← x.runUnsafe? ctx then
    return a
  else
    let e ← ctx.getRaisedException
    let e ← formatError e |>.run ctx
    throw <| IO.userError e
where
  formatError (e : PyBaseException) : PyBaseIO String := do
    -- Aims to mirror `print_exception`
    -- https://github.com/python/cpython/blob/v3.14.5/Python/pythonrun.c#L965
    -- TODO: include traceback & module name
    let ename ← id do
      let some n ← e.type.getQualName.run?
        | return "<unknown>"
      return n.toString
    let estr ← id do
      let some s ← e.str.run?
        | return "<exception str() failed>"
      return s.toString
    return if estr.isEmpty then ename else s!"{ename}: {estr}"

public instance : MonadEval PyIO IO := ⟨toIO⟩

end PyIO

namespace CPyIO

/--
Runs the {lean}`CPyIO` function in {lean}`IO`.

This is accomplished by lifting {lean}`CPyIO` to {lean}`PyIO` and
then running it via {lean}`PyIO.toIO`, so refer to it for more details.
-/
@[inline] public def toIO (x : CPyIO α) : IO α := do
  x.toPyIO.toIO

public instance : MonadEval CPyIO IO := ⟨toIO⟩

end CPyIO
