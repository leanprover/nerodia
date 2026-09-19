/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
import VersoManual

open Verso.Genre Manual

#doc (Manual) "Requirements" =>
%%%
tag := "requirements"
%%%

In order to build a Nerodia project on the latest version,
all of the following are required:

* Lean 4.34 or greater
* CPython 3.14 or greater (shared; not free-threaded)
* A C compiler which supports both (e.g., recent GCC or Clang;
  MSYS2's CLANG64 toolchain)

A standard CPython distribution should usually be sufficient.
[`uv`][1] and the [python.org installers][2] provide the necessary components.
Some system package managers may also require a separate development package
(e.g., `python3-dev`).

Nonetheless, it is possible to write a Nerodia project without Python or a C
compiler. These elements are only required to build and link the Python extension
(or to use  `precompileModules`) and thus could be delegated to a CI (e.g.,
GitHub Actions) that  can vendor these properly. Similarly, the Python extension
can be distributed as a prebuilt binary (i.e., wheel), so users of the extension
do not need Lean or a C compiler.

[1]: https://github.com/astral-sh/uv
[2]: https://www.python.org/downloads/
