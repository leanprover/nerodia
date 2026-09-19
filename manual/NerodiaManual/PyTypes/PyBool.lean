/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
module
public import VersoManual
import all Nerodia.Data.Types
import all Nerodia.Data.PyBool.Basic
meta import Nerodia.Control.PyIO
import NerodiaManual.Meta.Precompile

open Nerodia
open Verso.Genre Manual InlineLean

namespace NerodiaManual

#doc (Manual) "PyBool" =>
%%%
shortTitle := "PyBool"
tag := "PyBool"
%%%

{docstring Nerodia.PyBool}
{docstring Nerodia.Typing.bool}
{docstring Nerodia.mkPyBool}
{docstring Nerodia.PyBool.toBool}

# Boolean Constants
%%%
tag := "bool-constants"
%%%

Each boolean constant has its own singleton type which inherits the dot
notation of {lean}`PyBool` and is promotable to it.

```lean (name := pyTrueToBool)
#eval PyIO.toIO do
  return (← getPyTrue).toBool
```
```leanOutput pyTrueToBool
true
```

{docstring Nerodia.PyFalse}
{docstring Nerodia.Typing.false}
{docstring Nerodia.getPyFalse}

{docstring Nerodia.PyTrue}
{docstring Nerodia.Typing.true}
{docstring Nerodia.getPyTrue}
