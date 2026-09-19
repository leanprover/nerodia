/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
module
public import VersoManual
import all Nerodia.Control.PyIO.Basic
import all Nerodia.Data.PyBaseException.SPrint
import all Nerodia.Control.CPyIO.Basic

open Verso.Genre Manual

namespace NerodiaManual

#doc (Manual) "Monads" =>
%%%
tag := "monads"
htmlSplit := .never
%%%

The core monads of Nerodia are `PyIO` and its error-less variant `PyBaseIO`,
which equip `BaseIO` with a Python context. Each provides a utility function
to convert it back to its Python-less equivalent by allocating a temporary
Python context for the call. However, where possible, they should be run within
another Python-equipped monad to eficiently reuse its context.

{docstring Nerodia.PyIO}
{docstring Nerodia.PyBaseIO}

{docstring Nerodia.PyIO.toIO}
{docstring Nerodia.PyIO.toEIO}
{docstring Nerodia.PyBaseIO.toBaseIO}

# C Returns

Return contexts used for optimized C functions. They are not monads themselves,
but they automatically lift into their corresponding `PyIO`-stule monad (i.e.,
`CPyIO` to `PyIO`, `CPyBaseIO` to `PyBaseIO`).

{docstring Nerodia.CPyIO}
{docstring Nerodia.CPyBaseIO}
{docstring Nerodia.CPyUnitIO}
