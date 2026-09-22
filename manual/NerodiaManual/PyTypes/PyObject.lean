/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
module
public import VersoManual
import all Nerodia.Data.Py.Basic
import all Nerodia.Data.Typing.Raw
import all Nerodia.Data.PyObject.Basic

open Verso.Genre Manual

namespace NerodiaManual

#doc (Manual) "PyObject" =>
%%%
tag := "PyObject"
%%%

{docstring Nerodia.PyObject}
{docstring Nerodia.Typing.object}
{docstring Nerodia.PyObject.getType}
{docstring Nerodia.PyObject.repr}

# Conversions

{docstring Nerodia.PyObject.str}
{docstring Nerodia.PyObject.bytes}
{docstring Nerodia.PyObject.int}
{docstring Nerodia.PyObject.index}

# Attributes

{docstring Nerodia.PyObject.getAttr}
{docstring Nerodia.PyObject.getAttrByString}
{docstring Nerodia.PyObject.setAttr}
{docstring Nerodia.PyObject.setAttrByString}

# Function Calls

{docstring Nerodia.PyObject.call0}
{docstring Nerodia.PyObject.call1}
