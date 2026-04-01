/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

/-! # Nerodia -/

namespace Nerodia

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

/-- Returns a reference to the Python environment, initializing it if necessary. -/
@[extern "nerodia_py_context_get_or_init"]
private opaque getOrInit : BaseIO PyContext

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

/-! ## Monad -/

public class MonadPy (m : Type → Type u) where
  getPyContext : m PyContext

export MonadPy (getPyContext)

public instance [MonadLift m n] [MonadPy m] :MonadPy n where
  getPyContext := liftM (m := m) getPyContext

public abbrev PyT (m) := ReaderT PyContext m
public abbrev PyM := PyT BaseIO
public abbrev EPyM := OptionT PyM

namespace PyT

@[inline] public nonrec def run
  [MonadLiftT BaseIO m] [Monad m] (x : PyT m α) : m α
:= do x.run (← PyContext.getOrInit)

public instance [Monad m] : MonadPy (PyT m) := ⟨read⟩

end PyT

namespace PyM

@[inline] public nonrec def toBaseIO (x : PyM α) : BaseIO α := do
  x.run

public instance : MonadEval PyM BaseIO := ⟨PyM.toBaseIO⟩

end PyM

/-! ## PyTypeObject -/

namespace PyTypeObject

public instance : Coe PyTypeObject PyObject := ⟨toObject⟩

/-- Returns the qualified name of the type. -/
@[extern "nerodia_py_type_object_get_qual_name"]
public opaque getQualName (self : PyTypeObject) : PyM PyStrObject

@[extern "nerodia_py_type_object_is_heap_type"]
public opaque isHeapType (self : @& PyTypeObject) : Bool

@[extern "nerodia_py_type_object_is_immutable"]
public opaque isImmutable (self : @& PyTypeObject) : Bool

end PyTypeObject

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

/-! ## Type -/

/--
Returns the type of the object {lean}`self`.

This is equivalent to {lit}`type(self)` in Python.
-/
@[extern "nerodia_py_object_type"]
public opaque PyObject.type (self : @& PyObject) : PyTypeObject

/-! ## Strings -/


@[extern "nerodia_mk_string"]
public opaque mkString (s : @& String) : PyM PyStrObject

/--
Compute a string representation of the object {lean}`self`.

This is equivalent to the Python expression {lit}`str(self)`.
-/
@[extern "nerodia_py_object_str"]
public opaque PyObject.str (self : @& PyObject) : EPyM PyStrObject

/--
Compute a string representation of the object {lean}`self`.

This is equivalent to the Python expression {lit}`repr(self)`.
-/
@[extern "nerodia_py_object_repr"]
public opaque PyObject.repr (self : @& PyObject) : EPyM PyStrObject

/-- Returns the UTF8-encoded value of the Python string as a Lean {lean}`String`. -/
@[extern "nerodia_py_str_object_get_string"]
public opaque PyStrObject.getString (o : @& PyStrObject) : EPyM String

/-- Returns the UTF8-encoded value of the Python string as Python bytes. -/
@[extern "nerodia_py_str_object_decode_utf8"]
public opaque PyStrObject.decodeUtf8 (o : @& PyStrObject) : EPyM PyBytesObject

/-- Returns the bytes of {lean}`self` as a Lean {lean}`ByteArray`. -/
@[extern "nerodia_py_bytes_object_to_byte_array"]
public opaque PyBytesObject.toByteArray (self : @& PyBytesObject) : ByteArray

/-! ## Exception Handling -/

namespace PyContext

/-- Clears the current exception. Does nothing if there is none. -/
@[extern "nerodia_py_context_clear_error"]
public opaque clearError (ctx : @& PyContext) : BaseIO Unit

/--
Clears the current exception and returns it.
If none has been raised, returns {lean}`none`.
-/
@[extern "nerodia_py_context_get_raised_exception"]
public opaque getRaisedException? (ctx : PyContext) : BaseIO (Option PyObject)

end PyContext

@[inline, inherit_doc PyContext.clearError]
public def clearError [Bind m] [MonadPy m] [MonadLiftT BaseIO m] : m PUnit :=
  getPyContext >>= (·.clearError)

namespace EPyM

@[inline] public nonrec def toEIO (x : EPyM α) : EIO PyObject α := do
  let ctx ← PyContext.getOrInit
  match (← x.run ctx) with
  | some a => return a
  | none =>
    if let some ex ← ctx.getRaisedException? then
      throw ex
    else throw ctx.none

@[inline] public nonrec def toIO (x : EPyM α) : IO α := do
  let ctx ← PyContext.getOrInit
  match (← x.run ctx) with
  | some a => return a
  | none =>
    if let some ex ← ctx.getRaisedException? then
      throw <| IO.userError (← formatError ex ctx)
    else throw <| IO.userError "no exception raised"
where formatError (ex : PyObject) : PyM String := do
  -- Aims to mirror `print_exception`
  -- https://github.com/python/cpython/blob/v3.13.2/Python/pythonrun.c#L923
  -- TODO: include module name
  let exName ← id do
    let obj ← ex.type.getQualName
    match (← obj.getString) with
    | some s => return s
    | none =>
      clearError
      return "<unknown>"
  let exStr ← id do
    match (← ex.str) with
    | some s =>
      match (← s.getString) with
      | some s => return s
      | none =>
        clearError
        return "<exception decode failed>"
    | none =>
      clearError
      return "<exception str() failed>"
  return if exStr.isEmpty then exName else s!"{exName}: {exStr}"

public instance : MonadEval EPyM IO := ⟨EPyM.toIO⟩

end EPyM
