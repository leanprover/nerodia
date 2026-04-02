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
:= by exact p.nonempty_of_addr_ne_zero (by simpa [← addr_inj] using h)

end CPtr

/-! ## PyContext -/

private opaque PyContext.nonemptyType : NonemptyType.{0}

/--
Reference holder for the Python environment.
When this object is freed, Python will be unitialized.

Python objects created by Nerodia implicitly hold a reference to the context,
so the context will not be freed until all Python objects managed to Lean
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

/-- Wraps a raw Python object pointer into a memory-managed Lean object. -/
@[extern "nerodia_py_context_mk_object"]
public opaque mkObject {α} (ctx : PyContext) (ptr : CPtr α) (h : ¬ ptr.IsNull) : α :=
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
Returns a borrowed reference to Python object's raw unmaneged C pointer.

**This function is not memory safe.** It is the user's responsibility to
ensure that this pointer does not outlive {lean}`self`.
-/
@[inline] def borrow (self : PyObject) : CPtr PyObject :=
  ⟨self.addr, fun _ => ⟨self⟩⟩

/-- Returns a reference to the Python enviroment this object is within. -/
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

/-- Returns whether this type is a instance of {lit}`type`. -/
@[extern "nerodia_py_object_is_type_instance"]
public opaque isTypeInstance (self : @& PyObject) : Bool

/-- Returns whether this type is a instance of {lit}`str`. -/
@[extern "nerodia_py_object_is_str_instance"]
public opaque isStrInstance (self : @& PyObject) : Bool

end PyObject

/-! ## Builtin Types -/

/--
A Python type object.

In practice, these are instances of {lit}`type` or one of its subclasses,
but that is not guarenteed by the Limited API.

See https://docs.python.org/3/c-api/type.html#c.PyTypeObject
-/
public structure PyTypeObject extends toObject : PyObject where
  private innerMk ::
    deriving Nonempty

/-- A Python unicode object. That is, an instance of {lit}`str`. -/
public structure PyStrObject extends toObject : PyObject where
  private innerMk ::
    deriving Nonempty

/-- A Python bytes object. That is, an instance of {lit}`bytes`. -/
public structure PyBytesObject extends toObject : PyObject where
  private innerMk ::
    deriving Nonempty

/-! ## Builtin Objects -/

namespace PyContext

/-! ### Constants -/

private noncomputable opaque noneOpaque (ctx : PyContext) : PyObject

@[extern "nerodia_py_context_none"]
public opaque none (ctx : PyContext) : PyObject

/-! ### Type Objects -/

private noncomputable opaque typeTypeOpaque (ctx : PyContext) : PyTypeObject

/-- Returns a reference to the type of types (i.e., {lit}`type` in Python). -/
@[extern "nerodia_py_context_type_type"]
public opaque typeType (ctx : PyContext) : PyTypeObject

private noncomputable opaque strTypeOpaque (ctx : PyContext) : PyTypeObject

/-- Returns a reference to the unicode string type (i.e., {lit}`str` in Python). -/
@[extern "nerodia_py_context_str_type"]
public opaque strType (ctx : PyContext) : PyTypeObject

end PyContext

/-! ## Monad -/

public class MonadPy (m : Type → Type u) where
  getPyContext : m PyContext

export MonadPy (getPyContext)

public instance [MonadLift m n] [MonadPy m] :MonadPy n where
  getPyContext := liftM (m := m) getPyContext

@[inline, inherit_doc PyContext.clearError]
public def clearError [Bind m] [MonadPy m] [MonadLiftT BaseIO m] : m PUnit :=
  getPyContext >>= (·.clearError)

public abbrev PyT (m) := ReaderT PyContext m
public abbrev PyBaseIO := PyT BaseIO
public abbrev PyIO := PyT (EIO PyObject) -- TODO: restrict to exceptions


namespace PyT
public instance [Monad m] : MonadPy (PyT m) := ⟨read⟩
end PyT

@[inline] public def PyIO.toEIO (x : PyIO α) : EIO PyObject α := do
  x.run (← PyContext.init)

namespace PyBaseIO

@[inline] public def toPyIO (x : PyBaseIO α) : PyIO α := fun ctx =>
  x.run ctx

public instance : MonadLift PyBaseIO PyIO := ⟨toPyIO⟩

@[inline] public nonrec def toBaseIO (x : PyBaseIO α) : BaseIO α := do
  x.run (← PyContext.init)

public instance : MonadEval PyBaseIO BaseIO := ⟨PyBaseIO.toBaseIO⟩

end PyBaseIO

@[expose] -- for codegen
public def CPyT (m : Type → Type v) (α : Type) :=
  m (CPtr α)

namespace CPyT

@[inline] def mk (x : m (CPtr α)) : CPyT m α :=
  x

instance [Monad m] : Nonempty (CPyT m α) := ⟨mk <| pure .null⟩


@[inline] def runUnsafe (x : CPyT m α) : m (CPtr α) :=
  x

end CPyT

/-
Return context for external CPython functions.

Lifts only into `CPyT`, as it requires the Python context from it to run.
-/
public abbrev CPyIO (α) :=  CPyT BaseIO α

namespace CPyIO

@[inline] def mk (x : BaseIO (CPtr α)) : CPyIO α :=
  x

instance : Nonempty (CPyIO α) := ⟨mk <| pure .null⟩

@[inline] def toBaseIO (x : CPyIO α) : BaseIO (CPtr α) :=
  x

@[inline] public def toCPyT [MonadLiftT BaseIO m] (x : CPyIO α) : CPyT m α :=
  .mk x.toBaseIO

public instance [MonadLiftT BaseIO m] [Monad m] : MonadLift CPyIO (CPyT m) := ⟨toCPyT⟩

end CPyIO

/--
Clears the current exception and returns it.
If none has been raised, returns {lean}`none`.
-/
@[extern "nerodia_get_raised_exception"]
public opaque getRaisedException : CPyIO PyObject

namespace CPyT

@[inline] public def run
  [Monad m] [MonadPy m]
  [MonadExcept PyObject m] [MonadLiftT BaseIO m]  [MonadLiftT n m]
  (x : CPyT n α)
: m α := do
  let ctx ← getPyContext
  let ptr ← x.runUnsafe
  if h : ptr.IsNull then
    let eptr ← getRaisedException.runUnsafe
    if h : eptr.IsNull then
      -- should never happen
      throw ctx.none
    else
      throw <| ctx.mkObject eptr h
  else
    return ctx.mkObject ptr h

@[inline] public def run'
  [Monad m] [MonadPy m]
  [Alternative m] [MonadLiftT BaseIO m]  [MonadLiftT n m]
  (x : CPyT n α)
: m α := do
  let ctx ← getPyContext
  let ptr ← x.runUnsafe
  if h : ptr.IsNull then
    ctx.clearError
    failure
  else
    return ctx.mkObject ptr h

public abbrev toOptionT
  [Monad m] [MonadPy m]
  [MonadLiftT BaseIO m] [MonadLiftT n m]
  (x : CPyT n α)
: OptionT m α := x.run'

public abbrev toExceptT
  [Monad m] [MonadPy m]
  [MonadLiftT BaseIO m] [MonadLiftT n m]
  (x : CPyT n α)
: ExceptT PyObject m α := x.run

public abbrev run?
  [Monad m] [MonadPy m]
  [MonadLiftT BaseIO m] [MonadLiftT n m]
  (x : CPyT n α)
: m (Option α) := x.toOptionT.run

end CPyT

namespace CPyIO

@[inline] public def toPyIO (x : CPyIO α) : PyIO α :=
  x.run

public instance : MonadLift CPyIO PyIO := ⟨toPyIO⟩

@[inline] public def toEIO (x : CPyIO α) : EIO PyObject α :=
  have : MonadPy BaseIO := ⟨PyContext.init⟩
  x.run

end CPyIO

/-! ## PyTypeObject -/

namespace PyTypeObject

public instance : Coe PyTypeObject PyObject := ⟨toObject⟩

/-- Returns the qualified name of the type. -/
@[extern "nerodia_py_type_object_get_qual_name"]
public opaque getQualName (self : @& PyTypeObject) : CPyIO PyStrObject

@[extern "nerodia_py_type_object_is_heap_type"]
public opaque isHeapType (self : @& PyTypeObject) : Bool

@[extern "nerodia_py_type_object_is_immutable"]
public opaque isImmutable (self : @& PyTypeObject) : Bool

end PyTypeObject

/-! ## Type -/

/--
Returns the type of the object {lean}`self`.

This is equivalent to {lit}`type(self)` in Python.
-/
@[extern "nerodia_py_object_type"]
public opaque PyObject.type (self : @& PyObject) : PyTypeObject

/-! ## Strings -/

@[extern "nerodia_mk_py_str_object"]
public opaque mkPyStrObject (s : @& String) : CPyIO PyStrObject

/--
Compute a string representation of the object {lean}`self`.

This is equivalent to the Python expression {lit}`str(self)`.
-/
@[extern "nerodia_py_object_str"]
public opaque PyObject.str (self : @& PyObject) : CPyIO PyStrObject

/--
Compute a string representation of the object {lean}`self`.

This is equivalent to the Python expression {lit}`repr(self)`.
-/
@[extern "nerodia_py_object_repr"]
public opaque PyObject.repr (self : @& PyObject) : CPyIO PyStrObject

/-- Returns the UTF8-encoded value of {lean}`self` as a Lean {lean}`String`. -/
-- This function is pure because the string data of instances of `str` is immutable.
@[extern "nerodia_py_str_object_to_string"]
public opaque PyStrObject.toString (self : @& PyStrObject) : String

public instance : ToString PyStrObject := ⟨PyStrObject.toString⟩

/-- Returns the UTF8-encoded value of the Python string as Python bytes. -/
@[extern "nerodia_py_str_object_utf8_encode"]
public opaque PyStrObject.utf8Encode (self : @& PyStrObject) : CPyIO PyBytesObject

/-- Returns the bytes of {lean}`self` as a Lean {lean}`ByteArray`. -/
-- This function is pure because the bytes data of instances of `bytes` is immutable.
@[extern "nerodia_py_bytes_object_to_byte_array"]
public opaque PyBytesObject.toByteArray (self : @& PyBytesObject) : ByteArray

/-! ## Exception Handling -/

namespace PyIO

@[inline] public def toIO (x : PyIO α) : IO α := do
  let ctx ← PyContext.init
  match (← x.run ctx |>.toBaseIO) with
  | .ok a =>
    return a
  | .error e =>
    let e ← formatError e |>.run ctx
    throw <| IO.userError e
where
  formatError (e : PyObject) : PyBaseIO String := do
    -- Aims to mirror `print_exception`
    -- https://github.com/python/cpython/blob/v3.13.2/Python/pythonrun.c#L923
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

@[inline] public def toIO (x : CPyIO α) : IO α := do
  x.toPyIO.toIO

public instance : MonadEval CPyIO IO := ⟨toIO⟩

end CPyIO
