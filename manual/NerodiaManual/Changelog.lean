/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
import VersoManual

open Verso.Genre Manual

#doc (Manual) "Changelog" =>
%%%
tag := "changelog"
%%%

Highlights and breaking API changes for recent Nerodia versions appear here.
Nerodia versioning currently follows Lean's and thus does not follow [semantic
versioning][1]. Instead, a new version of Nerodia is released for each stable
Lean version (i.e., Nerodia 4.X.0 for Lean 4.X.Y-Z), usually once per month.

[1]: https://semver.org/

Nerodia publishes a Git tag for each Lean stable using a `v` prefix (e.g.,
`v4.33.X` for Lean `v4.33.X-Y`). If Nerodia needs to hot fix a bug, it will be
listed hera as a new patch version (e.g., Nerodia 4.33.1), and the Git tags
corresponding to the latest Lean stable release will be updated to point to it.
For example, if Nerodia 4.33.1 was released and the latest Lean stable is Lean
4.33.2, the `v4.33.2` tag will be updated but the `v4.33.1` tag will not.

# Nerodia 4.34.0 (in development)
%%%
tag := "4.34.0"
%%%

- Introduction of this reference manual.

- API for calling 0-arity and 1-arity Python functions
(see, `PyObject.call0`, `PyObject.call1`).

- Python integer support for fixed width Lean integer types
(e.g., `IntX`, `UIntX`).

# Nerodia 4.33.0
%%%
tag := "4.33.0"
%%%

- Initial release.
