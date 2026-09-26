/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
module
public import VersoManual
import all Nerodia.Data.Types
import all Nerodia.Data.PyBaseException.Basic
import all Nerodia.Data.PyBaseException.SPrint
import all Nerodia.Data.Exceptions

open Verso.Genre Manual

namespace NerodiaManual

#doc (Manual) "PyBaseException" =>
%%%
tag := "PyBaseException"
%%%

{docstring Nerodia.PyBaseException}
{docstring Nerodia.Typing.baseException}
{docstring Nerodia.PyBaseException.sprint}

# Raising Exceptions

{docstring Nerodia.raisePyRuntimeError}
{docstring Nerodia.raisePyEOFError}
{docstring Nerodia.raisePyTypeError}
{docstring Nerodia.raisePyValueError}
{docstring Nerodia.raisePyOSError}
