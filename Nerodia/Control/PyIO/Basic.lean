
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
Python [expects][1] exceptions to be handled and [requires][2] that futher
Python functions are not called while an exception is set.

[1]: https://docs.python.org/3/c-api/exceptions.html#exception-handling
[2]: https://github.com/python/cpython/issues/67759

Definitions that signal an exception without setting one are also unsafe.
While CPython [will][3] set its own exception if an FFI call returns `NULL`
without setting one, relying on this would be contray to the specification.

[3]: https://github.com/python/cpython/blob/v3.14.5/Objects/call.c#L31-L46
-/

namespace Nerodia

open Internal (PyContext)

/-! ## PyContextT -/

/--
Monad transfer to equip a monad with a Python context.

**API Caveat:** The definition of {name}`PyContextT` is not part of Nerodia's
public API. Nevertheless, it exposed due to the limitations of Lean's compiler.
-/
@[irreducible, expose] -- for codegen
public def PyContextT (m : Type → Type u) (α : Type) :=
  PyContext → m α

namespace Internal.Nerodia.PyContextT

unseal PyContextT in
/--
Constructs a {name}`PyContextT` from the equivalent {name}`ReaderT`.

**Thread Safety:** Users must ensure that the {name}`PyContext` does not
cross thread boundaries.
-/
@[always_inline]
public def ofReaderTUnsafe (x : ReaderT PyContext m α) : PyContextT m α :=
 x

unseal PyContextT in
/--
Converts a {name}`PyContextT` to the equivalent {name}`ReaderT`.

**Thread Safety:** Users must ensure that {name}`PyContext` does not
cross thread boundaries.
-/
@[always_inline]
public def toReaderTUnsafe (x : PyContextT m α) :  ReaderT PyContext m α :=
  x

open Internal in
/--
Runs the action within the given Python context.

**Thread Safety:** Users must ensure {lean}`ctx` does not cross thread boundaries.
-/
@[inline] public def runUnsafe (ctx : PyContext) (x : PyContextT m α)  : m α :=
  x.toReaderTUnsafe.run ctx

end Internal.Nerodia.PyContextT

namespace PyContextT

open Internal in
/-- Runs the monadic action within the given Python environment. -/
@[always_inline] public def run
  [Monad m] [MonadLiftT BaseIO m] (env : PyEnvironment) (x : PyContextT m α)
: m α := do x.toReaderTUnsafe.run (← PyContext.mk env)

open Internal in
/-- Runs the monadic action within a new Python context. -/
@[always_inline] public def run'
  [Monad m] [MonadLiftT BaseIO m] (x : PyContextT m α)
: m α := do x.toReaderTUnsafe.run (← PyContext.getOrInit)

open Internal in
/-- Lifts the action into a supporting monad. -/
@[always_inline] public def toM
  [Monad n] [MonadLiftT m n] [MonadPy n] (x : PyContextT m α)
: n α := do x.toReaderTUnsafe.run (← getPyContextUnsafe)

open Internal in
@[always_inline] public instance [Monad m] : MonadPy (PyContextT m) where
  getPyContextUnsafe := private .ofReaderTUnsafe read

public instance : MonadLift m (PyContextT m) :=
   inferInstanceAs (MonadLift m <| ReaderT PyContext m)

public instance : MonadFunctor m (PyContextT m) :=
  inferInstanceAs (MonadFunctor m <| ReaderT PyContext m)

public instance : MonadControl m (PyContextT m) :=
  inferInstanceAs (MonadControl m <| ReaderT PyContext m)

public instance[MonadExceptOf ε m] : MonadExceptOf ε (PyContextT m) :=
  inferInstanceAs (MonadExceptOf ε <| ReaderT PyContext m)

public instance [Monad m] : Monad (PyContextT m) :=
  inferInstanceAs (Monad <| ReaderT PyContext m)

public instance[Monad m] [LawfulMonad m] : LawfulMonad (PyContextT m) :=
  inferInstanceAs (LawfulMonad <| ReaderT PyContext m)

public instance [Monad m] [MonadAttach m] : MonadAttach (PyContextT m) :=
  inferInstanceAs (MonadAttach <| ReaderT PyContext m)

public instance [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] : LawfulMonadAttach (PyContextT m) :=
  inferInstanceAs (LawfulMonadAttach <| ReaderT PyContext m)

end PyContextT

/-! ## PyBaseIO -/

/--
A monad for impure code using Python. It cannot error.

**API Caveat:** The definition of {name}`PyBaseIO` is not part of Nerodia's
public API. Nevertheless, it exposed due to the limitations of Lean's compiler.
-/
@[irreducible, expose] -- for codegen
public def PyBaseIO :=
  PyContextT BaseIO
  deriving Monad, MonadPy

namespace Internal.Nerodia.PyBaseIO

unseal PyBaseIO in
/-- Constructs a {name}`PyBaseIO` from the equivalent {name}`PyContextT`. --/
@[always_inline] public def ofPyContextT (x : PyContextT BaseIO α) : PyBaseIO α :=
  x

unseal PyBaseIO in
/-- Converts a {name}`PyBaseIO` to the equivalent {name}`PyContextT`. -/
@[always_inline] public def toPyContextT (x : PyBaseIO α) : PyContextT BaseIO α :=
  x

open Internal in
/--
Runs the {name}`PyBaseIO` action within the given Python context.

**Thread Safety:** Users must ensure {lean}`ctx` does not cross thread boundaries.
-/
@[inline] public def runUnsafe (ctx : PyContext) (x : PyBaseIO α)  : BaseIO α :=
  x.toPyContextT.toReaderTUnsafe.run ctx

end Internal.Nerodia.PyBaseIO

open Internal in
/-- Lifts a {name}`BaseIO` action into {name}`PyBaseIO`. -/
@[inline] public def BaseIO.toPyBaseIO (x : BaseIO α) : PyBaseIO α  :=
  .ofPyContextT x

public instance : MonadLift BaseIO PyBaseIO := ⟨BaseIO.toPyBaseIO⟩

namespace PyBaseIO

open Internal in
/-- Runs the action within the given Python environment. -/
@[inline] public def run (env : PyEnvironment) (x : PyBaseIO α) : BaseIO α := do
  x.toPyContextT.run env

open Internal in
/-- Runs the {name}`PyBaseIO` action in {name}`BaseIO`, using a new Python context. -/
@[inline] public def toBaseIO (x : PyBaseIO α) : BaseIO α := do
  x.toPyContextT.run'

public instance : MonadEval PyBaseIO BaseIO := ⟨PyBaseIO.toBaseIO⟩

open Internal in
/-- Lifts the action into a supporting monad. -/
@[inline] public def toM
  [Monad n] [MonadLiftT BaseIO n] [MonadPy n]  (x : PyBaseIO α)
: n α := x.toPyContextT.toM

end PyBaseIO

/-! ## PyIO -/

/--
The primary monad for code using Python.

**API Caveat:** The definition of {name}`PyIO` is not part of Nerodia's
public API. Nevertheless, it exposed due to the limitations of Lean's compiler.
-/
@[irreducible, expose] -- for codegen
public def PyIO :=
  OptionT <| PyBaseIO
  deriving Monad, MonadPy

namespace Internal.Nerodia.PyIO

unseal PyIO in
/--
Constructs a {name}`PyIO` from the equivalent {name}`PyContextT`.

**Safety:** Users should ensure that an exception is set on {lean}`x`'s failure.
-/
@[inline] public def ofOptionTUnsafe (x : OptionT PyBaseIO α) : PyIO α :=
  x


unseal PyIO in
/--
Converts a {name}`PyIO` to the equivalent {name}`PyContextT`.

**Safety:** Users must handle the raised exception on failure.
-/
@[inline] public def toOptionTUnsafe (x : PyIO α) : OptionT PyBaseIO α :=
  x

open Internal Nerodia in
/--
Runs the {name}`PyIO` function, returning {name}`none` if an exception was raised.

**Safety:** Users must handle a raised exception.
-/
@[inline] public def toPyBaseIOUnsafe?  (x : PyIO α) : PyBaseIO (Option α) :=
  x.toOptionTUnsafe.run


open Internal Nerodia in
/--
Runs the {name}`PyIO` function, returning {name}`none` if an exception was raised.

**Safety**
* **Correctness:** Users must handle a raised exception.
* **Thread:** Users must ensure that {lean}`ctx` does not cross thread boundaries.
-/
@[inline] public def runUnsafe? (ctx : PyContext) (x : PyIO α) : BaseIO (Option α) :=
  x.toPyBaseIOUnsafe?.runUnsafe ctx

/--
Constructs a {name}`PyIO` that fails.

**Safety:** Users should ensure that an exception is set.
-/
@[inline] public def failureUnsafe : PyIO α :=
  ofOptionTUnsafe failure

end Internal.Nerodia.PyIO

open Internal in
/-- Lifts a {name}`BaseIO` action into {name}`PyIO`. -/
@[inline] public def BaseIO.toPyIO (x : BaseIO α) : PyIO α  :=
  .ofOptionTUnsafe x

public instance : MonadLift BaseIO PyIO := ⟨BaseIO.toPyIO⟩

/-- Lifts a {name}`PyBaseIO` action into {name}`PyIO`. -/
@[inline] public def PyBaseIO.toPyIO (x : PyBaseIO α) : PyIO α :=
  x.toM

public instance : MonadLift PyBaseIO PyIO := ⟨PyBaseIO.toPyIO⟩
