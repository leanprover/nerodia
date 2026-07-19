
/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Control.MonadPy

/-! # Python Monads -/

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

namespace Nerodia

open Internal (PyContext)

/-- The primary monad for impure code using Python. -/
@[expose] -- for codegen
public def PyIO (α) :=
  ReaderT PyContext BaseIO (Option α)

namespace PyIO

/--
Constructs a {lean}`PyIO` from its definition.

**Safety**
* **Correctness:** Users should ensure that an exception is set on {lean}`x`'s failure.
* **Thread:** Users must ensure that the {name}`PyContext` does not cross thread boundaries.
-/
@[inline] public def mkUnsafe (x : ReaderT PyContext (OptionT BaseIO) α) : PyIO α :=
  x

/--
Runs the {lean}`PyIO` function, returning {lean}`none` if an exception was raised.

**Safety**
* **Correctness:** Users must handle a raised exception.
* **Thread:** Users must ensure that {lean}`ctx` does not cross thread boundaries.
-/
@[inline] public def runUnsafe? (ctx : PyContext) (x : PyIO α) : BaseIO (Option α) :=
  x ctx

/--
Constructs a {lean}`PyIO` that fails.

**Safety:** Users should ensure that an exception is set.
-/
@[inline] public def failureUnsafe : PyIO α :=
  mkUnsafe failure

@[inline] protected def getPyContextUnsafe : PyIO PyContext :=
  mkUnsafe read

public instance : MonadPy PyIO where
  getPyContextUnsafe := private PyIO.getPyContextUnsafe

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

@[inline] protected def getPyContextUnsafe : PyBaseIO PyContext :=
  mkUnsafe read

public instance : MonadPy PyBaseIO where
  getPyContextUnsafe := private PyBaseIO.getPyContextUnsafe

def test : PyBaseIO Internal.PyContext :=
  Internal.getPyContextUnsafe

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
