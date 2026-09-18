/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
import VersoManual

import NerodiaManual.Changelog
import NerodiaManual.Requirements
import NerodiaManual.Stability
import NerodiaManual.Tutorials

open Verso.Genre Manual

#doc (Manual) "Nerodia Reference Manual" =>
%%%
authors := ["Mac Malone"]
shortTitle := "Nerodia Reference Manual"
%%%

Nerodia is a library for Lean/Python FFI inspired by [PyO3][1].
It utilizes Lake, Lean's build system, to provide seamless integration.
The name of the library comes from the genus _Nerodia_, a type of water snake.
That is, a snake you would find in a lake.

![Nerodia logo](static/nerodia.svg)

This manual provides tutorials to help new users get started, a general
outline of Nerodia's structure, and a detailed reference of the Python API
it exposes.

*Important:* Nerodia (and this reference mnaual) is still a *work-in-progress*
and currently has a very  limited API. It is released to the public primarily
as a proof-of-concept and to obtain feedback on its design and build process.

[1]: https://github.com/PyO3/pyo3

{include 0 NerodiaManual.Requirements}
{include 0 NerodiaManual.Stability}
{include 0 NerodiaManual.Changelog}
{include 0 NerodiaManual.Tutorials}
