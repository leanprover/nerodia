/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
module
public import VersoManual
import NerodiaManual.PyTypes.PyBaseException
import NerodiaManual.PyTypes.PyBytes
import NerodiaManual.PyTypes.PyBool
import NerodiaManual.PyTypes.PyInt
import NerodiaManual.PyTypes.PyModule
import NerodiaManual.PyTypes.PyNone
import NerodiaManual.PyTypes.PyObject
import NerodiaManual.PyTypes.PyStr
import NerodiaManual.PyTypes.PyType

open Verso.Genre Manual

namespace NerodiaManual

#doc (Manual) "Python Types" =>
%%%
tag := "python-types"
%%%

Nerodia exposes the basic types of Python as Lean types with a `Py` prefix.

{include 0 NerodiaManual.PyTypes.PyBaseException}
{include 0 NerodiaManual.PyTypes.PyBool}
{include 0 NerodiaManual.PyTypes.PyBytes}
{include 0 NerodiaManual.PyTypes.PyInt}
{include 0 NerodiaManual.PyTypes.PyModule}
{include 0 NerodiaManual.PyTypes.PyNone}
{include 0 NerodiaManual.PyTypes.PyObject}
{include 0 NerodiaManual.PyTypes.PyStr}
{include 0 NerodiaManual.PyTypes.PyType}
