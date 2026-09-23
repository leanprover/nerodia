/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
module
import all Init.Prelude
import all Init.System.IO
import all Init.Data.Int.Basic
import all Init.Data.SInt.Basic
public import VersoManual
import Nerodia.Data.Types

open Nerodia
open Verso.Genre Manual InlineLean

namespace NerodiaManual

variable {T : Type}

#doc (Manual) "Type Conversions" =>
%%%
tag := "type-conversions"
htmlSplit := .never
%%%

When using {ref "annotations"}[annotations] like `@[py_moddule_fn]` or
`@[py_module_attr]`, Nerodia constructs a Python signature from the Lean
definition's signature, translating the Lean types of arguments and results
into Python types. In the simple case, a Nerodia type representing a Python type
(e.g., {lean}`PyBool`) is translated directly to its corresponding Python type.
Standard Lean types (e.g., {lean}`Bool`), on the other hand, require conversion,
and Nerodia follows the mapping below in doing so.

:::table (tag := "type-conversions-table")

* * Lean Type
  * Python Argument Type
  * Python Result Type

* * {lean}`IO T`
  * —
  * `T`
* * {lean}`BaseIO T`
  * —
  * `T`

* * {lean}`Unit`
  * —
  * `None`
* * {lean}`Empty`
  * `Never`
  * `Never`
* * {lean}`Option T`
  * `T | None`
  * `T | None`

* * {lean}`Bool`
  * `bool`
  * `bool`
* * {lean}`String`
  * `str`
  * `str`
* * {lean}`ByteArray`
  * `Buffer`
  * `bytes`

* * {lean}`Int`
  * `int`
  * `int`
* * {lean}`Nat`
  * `int`
  * `int`
* * {lean}`Fin`
  * `int`
  * `int`
* * {tech}`IntX`
  * `int`
  * `int`
* * {tech}`UIntX`
  * `int`
  * `int`

:::

* {deftech}`IntX`, fixed-width integers:
  {lean}`ISize`, {lean}`Int64`, {lean}`Int32`, {lean}`Int16`, {lean}`Int8`
* {deftech}`UIntX`, fixed-width unsigned integers:
  {lean}`USize`, {lean}`UInt64`, {lean}`UInt32`, {lean}`UInt16`, {lean}`UInt8`
