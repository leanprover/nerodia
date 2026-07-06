/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia

namespace Nerodia

/-!
This module initializes a persistent Python environment and uses this
to render aspects of the Python API pure (e.g., constants like {lit}`None`).
-/

/-- A persistent Python environment. -/
public initialize pyEnv : PyEnvironment ←
  PyEnvironment.getOrInit

-- Pure monads can then make use of the Python environment.
public instance : MonadPyEnv Id := ⟨pure pyEnv⟩

/-- Python's {lit}`None` constant as a pure definition. -/
public abbrev pyNone : PyObject := pyEnv.none
