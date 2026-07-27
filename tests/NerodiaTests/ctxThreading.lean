/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Claude Code
-/
import Nerodia

open Nerodia
open Internal (PyThreadCtx)

/-!
# Interweaving Python Contexts & Threads

Tests {name}`PyThreadCtx`'s bookkeeping: nesting multiple contexts on one
thread, letting a Python object outlive the context that created it, and
concurrent initialization/finalization races across threads.
-/

/-!
## Multiple contexts on one thread

Contexts must be arbitrarily nestable and freeable in any order without
releasing the GIL early (unlike Python's GIL state).
-/

#guard_msgs in
#eval show IO Unit from do
  let c1 ← PyThreadCtx.getOrInit -- should take the GIL
  let c2 ← PyThreadCtx.getOrInit -- should reuse the GIL state
  Runtime.hold c1 -- release c1 here (should NOT release the GIL)
  Runtime.hold c2 -- release c2 here (fatal if GIL already released)

/-!
## Object outlives its creating context

A Python object created inside one context should keep the environment alive
after that context is finalized and remain usable.
-/

/-- info: "outlives" -/
#guard_msgs in
#eval show IO String from do
  let obj ← PyIO.toIO do
    mkPyStr "outlives"
  -- The creating context was dropped when `toIO` returned.
  -- Verify `obj` is still alive.
  return obj.toString

/-!
## Cross-thread object finalization

Python objects should be freeable on a separate thread from where they were
created and even in a thread without a Python context. This means acquiring
and releasing the GIL on a separate thread during object finalization.
-/

#guard_msgs in
#eval show IO Unit from do
  -- Three objects: the last frees the environment, the first two do not.
  let n := 3
  let task ← IO.asTask (prio := .dedicated) <| PyIO.toIO do
    let mut objs : Array PyStr := #[]
    for i in [0:n] do
      objs := objs.push (← mkPyStr s!"obj-{i}")
    return objs
  let objs ← match task.get with
    | .ok objs => pure objs
    | .error e => throw e
  -- The task's context is gone, but the objects are kept alive until here.
  -- Dropping them afterwards finalizes them on this context-less thread.
  Runtime.hold objs

/-!
## Concurrent initialization and finalization

Runs Python initialization against a concurrent finalization. This stages a
race every iteration, but does not guarantee one. If a race occurs, an improper
deadlock will hang and an improper use-after-finalize will crash.

A fully deterministic test of the race is impossible from Lean.
-/

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let mut ok := true
  for _ in [0:16] do
    let ready : IO.Promise Unit ← IO.Promise.new
    let go : IO.Promise Unit ← IO.Promise.new
    let b ← IO.asTask (prio := .dedicated) do
      -- Acquire the context and signal readiness
      let ctx ← PyThreadCtx.getOrInit
      ready.resolve ()
      IO.wait go.result!
      -- On notification, drop it (which triggers finalize).
      Runtime.hold ctx
    -- Once the task holds the only context, release it and initialize here at
    -- the same time, racing this thread's `getOrInit` against the task's finalize.
    IO.wait ready.result!
    go.resolve ()
    let _ ← PyThreadCtx.getOrInit
    match b.get with
    | .ok _ => pure ()
    | .error e =>
      IO.println e
      ok := false
  return ok
