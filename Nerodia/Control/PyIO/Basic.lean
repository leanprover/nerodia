
/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Control.MonadPy

/-! # Python Monads -/

/-
**Implementation Note**

Any definition that signals an exception without handling it is unsafe.
Python [expects][1] exceptions to be handled and [requires][2] that further
Python functions are not called while an exception is set.

[1]: https://docs.python.org/3/c-api/exceptions.html#exception-handling
[2]: https://github.com/python/cpython/issues/67759

Definitions that signal an exception without setting one are also unsafe.
While CPython [will][3] set its own exception if an FFI call returns `NULL`
without setting one, relying on this would be contrary to the specification.

[3]: https://github.com/python/cpython/blob/v3.14.5/Objects/call.c#L31-L46
-/

namespace Nerodia

open Internal (PyThreadCtx)

/-! ## PyThreadCtxT -/

/--
Monad transformer to equip a monad with a Python context.

**API Caveat:** The definition of {name}`PyThreadCtxT` is not part of Nerodia's
public API. Nevertheless, it is exposed due to the limitations of Lean's compiler.
-/
@[irreducible, expose] -- for codegen
public def PyThreadCtxT (m : Type → Type u) (α : Type) :=
  @& PyThreadCtx → m α

namespace Internal.Nerodia.PyThreadCtxT

unseal PyThreadCtxT in
/--
Constructs a {name}`PyThreadCtxT` from the equivalent {name}`ReaderT`.

**Thread Safety:** Users must ensure that the {name}`PyThreadCtx` does not
cross thread boundaries.
-/
@[always_inline]
public def ofReaderTUnsafe (x : ReaderT PyThreadCtx m α) : PyThreadCtxT m α :=
 x

unseal PyThreadCtxT in
/--
Converts a {name}`PyThreadCtxT` to the equivalent {name}`ReaderT`.

**Thread Safety:** Users must ensure that {name}`PyThreadCtx` does not
cross thread boundaries.
-/
@[always_inline]
public def toReaderTUnsafe (x : PyThreadCtxT m α) :  ReaderT PyThreadCtx m α :=
  x

open Internal in
/--
Runs the action within the given Python context.

**Thread Safety:** Users must ensure {lean}`ctx` does not cross thread boundaries.
-/
@[inline] public def runUnsafe (ctx : PyThreadCtx) (x : PyThreadCtxT m α)  : m α :=
  x.toReaderTUnsafe.run ctx

end Internal.Nerodia.PyThreadCtxT

namespace PyThreadCtxT

open Internal in
/-- Runs the monadic action within the given Python environment. -/
@[always_inline] public def run
  [Monad m] [MonadLiftT BaseIO m] (env : PyEnvironment) (x : PyThreadCtxT m α)
: m α := do x.toReaderTUnsafe.run (← PyThreadCtx.mk env)

open Internal in
/-- Runs the monadic action within a new Python context. -/
@[always_inline] public def run'
  [Monad m] [MonadLiftT BaseIO m] (x : PyThreadCtxT m α)
: m α := do x.toReaderTUnsafe.run (← PyThreadCtx.getOrInit)

open Internal in
/-- Lifts the action into a supporting monad. -/
@[always_inline] public def toM
  [Monad n] [MonadLiftT m n] [MonadPy n] (x : PyThreadCtxT m α)
: n α := do x.toReaderTUnsafe.run (← getPyThreadCtxUnsafe)

open Internal in
@[always_inline] public instance [Monad m] : MonadPy (PyThreadCtxT m) where
  getPyThreadCtxUnsafe := private .ofReaderTUnsafe read

public instance : MonadLift m (PyThreadCtxT m) :=
   inferInstanceAs (MonadLift m <| ReaderT PyThreadCtx m)

public instance : MonadFunctor m (PyThreadCtxT m) :=
  inferInstanceAs (MonadFunctor m <| ReaderT PyThreadCtx m)

public instance : MonadControl m (PyThreadCtxT m) :=
  inferInstanceAs (MonadControl m <| ReaderT PyThreadCtx m)

public instance[MonadExceptOf ε m] : MonadExceptOf ε (PyThreadCtxT m) :=
  inferInstanceAs (MonadExceptOf ε <| ReaderT PyThreadCtx m)

public instance [Monad m] : Monad (PyThreadCtxT m) :=
  inferInstanceAs (Monad <| ReaderT PyThreadCtx m)

public instance[Monad m] [LawfulMonad m] : LawfulMonad (PyThreadCtxT m) :=
  inferInstanceAs (LawfulMonad <| ReaderT PyThreadCtx m)

public instance [Monad m] [MonadAttach m] : MonadAttach (PyThreadCtxT m) :=
  inferInstanceAs (MonadAttach <| ReaderT PyThreadCtx m)

public instance [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] : LawfulMonadAttach (PyThreadCtxT m) :=
  inferInstanceAs (LawfulMonadAttach <| ReaderT PyThreadCtx m)

end PyThreadCtxT

/-! ## PyBaseIO -/

/--
A monad for impure code using Python. It cannot error.

**API Caveat:** The definition of {name}`PyBaseIO` is not part of Nerodia's
public API. Nevertheless, it is exposed due to the limitations of Lean's compiler.
-/
@[irreducible, expose] -- for codegen
public def PyBaseIO :=
  PyThreadCtxT BaseIO

public instance : Monad PyBaseIO := inferInstanceAs (Monad <| PyThreadCtxT BaseIO)
public instance : MonadPy PyBaseIO := inferInstanceAs (MonadPy <| PyThreadCtxT BaseIO)

namespace Internal.Nerodia.PyBaseIO

unseal PyBaseIO in
/-- Constructs a {name}`PyBaseIO` from the equivalent {name}`PyThreadCtxT`. --/
@[always_inline] public def ofPyThreadCtxT (x : PyThreadCtxT BaseIO α) : PyBaseIO α :=
  x

unseal PyBaseIO in
/-- Converts a {name}`PyBaseIO` to the equivalent {name}`PyThreadCtxT`. -/
@[always_inline] public def toPyThreadCtxT (x : PyBaseIO α) : PyThreadCtxT BaseIO α :=
  x

open Internal in
/--
Runs the {name}`PyBaseIO` action within the given Python context.

**Thread Safety:** Users must ensure {lean}`ctx` does not cross thread boundaries.
-/
@[inline] public def runUnsafe (ctx : PyThreadCtx) (x : PyBaseIO α)  : BaseIO α :=
  x.toPyThreadCtxT.toReaderTUnsafe.run ctx

end Internal.Nerodia.PyBaseIO

open Internal in
/-- Lifts a {name}`BaseIO` action into {name}`PyBaseIO`. -/
@[inline] public def BaseIO.toPyBaseIO (x : BaseIO α) : PyBaseIO α  :=
  .ofPyThreadCtxT x

public instance : MonadLift BaseIO PyBaseIO := ⟨BaseIO.toPyBaseIO⟩

namespace PyBaseIO

open Internal in
/-- Runs the action within the given Python environment. -/
@[inline] public def run (env : PyEnvironment) (x : PyBaseIO α) : BaseIO α := do
  x.toPyThreadCtxT.run env

open Internal in
/-- Runs the {name}`PyBaseIO` action in {name}`BaseIO`, using a new Python context. -/
@[inline] public def toBaseIO (x : PyBaseIO α) : BaseIO α := do
  x.toPyThreadCtxT.run'

public instance : MonadEval PyBaseIO BaseIO := ⟨PyBaseIO.toBaseIO⟩

open Internal in
/-- Lifts the action into a supporting monad. -/
@[inline] public def toM
  [Monad n] [MonadLiftT BaseIO n] [MonadPy n]  (x : PyBaseIO α)
: n α := x.toPyThreadCtxT.toM

end PyBaseIO

/-! ## PyIO -/

/--
The primary monad for code using Python.

**API Caveat:** The definition of {name}`PyIO` is not part of Nerodia's
public API. Nevertheless, it is exposed due to the limitations of Lean's compiler.
-/
@[irreducible, expose] -- for codegen
public def PyIO :=
  OptionT <| PyBaseIO

public instance : Monad PyIO := inferInstanceAs (Monad <| OptionT PyBaseIO)
public instance : MonadPy PyIO := inferInstanceAs (MonadPy <| OptionT PyBaseIO)

namespace Internal.Nerodia.PyIO

unseal PyIO in
/--
Constructs a {name}`PyIO` from the equivalent {name}`OptionT`.

**Safety:** Users should ensure that an exception is set on {lean}`x`'s failure.
-/
@[inline] public def ofOptionTUnsafe (x : OptionT PyBaseIO α) : PyIO α :=
  x

/--
Constructs a {name}`PyIO` from the equivalent {name}`PyBaseIO`.

**Safety:** Users should ensure that an exception is set on {lean}`x`'s failure.
-/
@[inline] public def ofPyBaseIOUnsafe (x : PyBaseIO (Option α)) : PyIO α :=
  ofOptionTUnsafe <| .mk x

unseal PyIO in
/--
Converts a {name}`PyIO` to the equivalent {name}`OptionT`.

**Safety:** Users must handle the raised exception on failure.
-/
@[inline] public def toOptionTUnsafe (x : PyIO α) : OptionT PyBaseIO α :=
  x

open Internal in
/--
Runs the {name}`PyIO` function, returning {name}`none` if an exception was raised.

**Safety:** Users must handle a raised exception.
-/
@[inline] public def toPyBaseIOUnsafe?  (x : PyIO α) : PyBaseIO (Option α) :=
  x.toOptionTUnsafe.run


open Internal in
/--
Runs the {name}`PyIO` function, returning {name}`none` if an exception was raised.

**Safety**
* **Correctness:** Users must handle a raised exception.
* **Thread:** Users must ensure that {lean}`ctx` does not cross thread boundaries.
-/
@[inline] public def runUnsafe? (ctx : PyThreadCtx) (x : PyIO α) : BaseIO (Option α) :=
  x.toPyBaseIOUnsafe?.runUnsafe ctx

/--
Constructs a {name}`PyIO` that fails.

**Safety:** Users should ensure that an exception is set.
-/
@[inline] public def failureUnsafe : PyIO α :=
  ofOptionTUnsafe failure

end Internal.Nerodia.PyIO

open Internal in
public instance : Nonempty (PyIO α) := ⟨.failureUnsafe⟩

open Internal in
/-- Lifts a {name}`PyBaseIO` action into {name}`PyIO`. -/
@[inline] public def PyBaseIO.toPyIO (x : PyBaseIO α) : PyIO α :=
  .ofOptionTUnsafe x

public instance : MonadLift PyBaseIO PyIO := ⟨PyBaseIO.toPyIO⟩

/-- Lifts a {name}`BaseIO` action into {name}`PyIO`. -/
@[inline] public def BaseIO.toPyIO (x : BaseIO α) : PyIO α  :=
  BaseIO.toPyBaseIO x |>.toPyIO

public instance : MonadLift BaseIO PyIO := ⟨BaseIO.toPyIO⟩
