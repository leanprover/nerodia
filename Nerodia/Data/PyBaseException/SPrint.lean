/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Data.Types
public import Nerodia.Control.CPyIO
import Nerodia.Data.PyObject.Basic
import Nerodia.Data.PyModule.Basic
import Nerodia.Data.PyStr.Basic
import Nerodia.Data.PyType.Basic
meta import Nerodia.Internal.ViewMethod

/-! # Formatted Exceptions -/

namespace Nerodia

/--
Formats the exception as a Lean string,
closely mirroring how Python would print it.
-/
@[view_method]
public def PyBaseException.sprint (e : PyBaseException) : PyBaseIO String := do
  -- Aims to mirror `print_exception`
  -- https://github.com/python/cpython/blob/v3.14.5/Python/pythonrun.c#L965
  -- TODO: include traceback & module name
  let ename ← id do
    let some n ← (← e.getType).getQualName.toM?
      | return "<unknown>"
    return n.toString
  let estr ← id do
    let some s ← e.str.toM?
      | return "<exception str() failed>"
    return s.toString
  return if estr.isEmpty then ename else s!"{ename}: {estr}"

namespace PyIO

/--
Runs the {lean}`PyIO` function in {lean}`IO`.

If an exception is raised, it will be formatted in the standard Python manner
(see {name}`PyBaseException.sprint`) and reported as an {lean}`IO.userError`.

This creates a new temporary Python context for the call.
As such, it should only be used when a Python context is not available.
For instance, this can be used in {lit}`main` to run a {lean}`PyIO` function.
It is also used to run {lean}`PyIO` in `#eval`.

**Example**
```lean
def main : IO Unit := do
  let pyVer ← Nerodia.PyIO.toIO do
    let sys ← Nerodia.import "sys"
    let ver ← sys.getAttrByString "version"
    return (← ver.str).toString
  IO.println pyVer
```
-/
@[inline] public def toIO (x : PyIO α) : IO α :=
  PyThreadCtxT.run' <| x.tryCatchM fun e => do
    throw (IO.userError (← e.sprint.toM))

public instance : MonadEval PyIO IO := ⟨toIO⟩

end PyIO

namespace CPyIO

/--
Runs the {lean}`CPyIO` function in {lean}`IO`.
See {lean}`PyIO.toIO` for details.
-/
@[inline] public def toIO (x : CPyIO α) : IO α := do
  x.toPyIO.toIO

public instance : MonadEval CPyIO IO := ⟨toIO⟩

end CPyIO
