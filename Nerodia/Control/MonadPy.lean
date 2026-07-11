/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Context

/-! # Python Monad Type Class -/

namespace Nerodia

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
