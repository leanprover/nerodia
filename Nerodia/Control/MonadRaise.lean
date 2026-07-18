/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Types

namespace Nerodia

/-- Type class for monads that can raise Python exceptions. -/
public class MonadRaise (m : Type u → Type v) where
   /-- Raises the exception {lean}`e`.-/
  raise (e : PyBaseException) : m α

 /-- Raises the exception {lean}`e`.-/
@[inline] public def raise [MonadRaise m] [ToPyBaseException ε] (e : ε) : m α :=
  MonadRaise.raise (toPy e)
