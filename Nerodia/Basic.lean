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
@[extern "nerodia_py_context_get"]
opaque get : BaseIO PyContext

end PyContext

/-! ## PyM -/

public abbrev PyM := ReaderT PyContext BaseIO

@[inline] public nonrec def PyM.run (x : PyM α) : BaseIO α := do
  x.run (← PyContext.get)

public instance : MonadEval PyM BaseIO := ⟨PyM.run⟩

/-! ## PyObject -/

private opaque PyObject.nonemptyType : NonemptyType.{0}

/--
A Python object.

See https://docs.python.org/3/c-api/structures.html#c.PyObject
-/
public def PyObject := PyObject.nonemptyType.type

public instance : Nonempty PyObject := PyObject.nonemptyType.property

/-! ## Basic UTils -/

@[extern "nerodia_mk_string"]
public opaque mkString (s : @& String) : PyM PyObject

@[extern "nerodia_repr"]
public opaque repr (s : @& PyObject) : BaseIO String
