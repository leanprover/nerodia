/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

/-! # Python Context -/

namespace Nerodia

/-! ## PyEnvironment -/

/--
Reference holder for the Python environment.

Python objects created by Nerodia implicitly hold a reference to the Python
environment. Thus, the Python environment will not be finalized until all Python
objects managed by Lean are freed.
-/
public structure PyEnvironment where
  private mk ::
    private data : Dynamic
    deriving Nonempty

namespace PyEnvironment

/--
Returns a reference to the Python environment.

If no Python environment exists yet, it will be initialized.
-/
@[extern "nerodia_py_environment_get_or_init"]
public opaque getOrInit : BaseIO PyEnvironment

end PyEnvironment

/-! ## PyContext -/

structure PyContext.Model where
  mk ::
    env : PyEnvironment
    data : Dynamic
    deriving Nonempty

/--
Reference holder for the Python environment ({name}`PyEnvironment`)
and the global interpreter lock (GIL).

**Not thread safe.** As a {name}`PyContext` object holds a lock (the GIL),
it must not be marked persistent or multi-threaded. Any attempt to do so
will emit a fatal panic. Nerodia ensures this within its API, and users are
not expected to manage {name}`PyContext` objects manually.
-/
public structure PyContext where
  private ofModel ::
    private toModel : PyContext.Model
    deriving Nonempty

namespace PyContext

noncomputable opaque mkOpaque (env : PyEnvironment) : BaseIO PyContext

/--
Constructs a Python context from a Python environment,
ensuring this thread has the global interpreter lock (GIL).
-/
@[extern "nerodia_py_context_mk"]
public def mk (env : @& PyEnvironment) : BaseIO PyContext :=
  (ofModel {·.toModel with env}) <$> mkOpaque env

/--
Returns a reference to this thread's Python context,
ensuring the thread has the global interpreter lock (GIL).

If no Python environment exists yet, it will be initialized.
-/
@[extern "nerodia_py_context_get_or_init"]
public def getOrInit : BaseIO PyContext := do
  mk (← PyEnvironment.getOrInit)

/-- Returns a reference to the Python environment. -/
@[extern "nerodia_py_context_env"]
public def env (ctx : @& PyContext) : PyEnvironment :=
  ctx.toModel.env

end PyContext
