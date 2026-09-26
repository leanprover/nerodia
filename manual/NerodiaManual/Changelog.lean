/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/

import VersoManual
import Nerodia

open Nerodia Internal
open Verso.Genre Manual InlineLean

#doc (Manual) "Changelog" =>
%%%
tag := "changelog"
htmlSplit := .never
%%%

Highlights and breaking API changes for recent Nerodia versions appear here.
Nerodia versioning currently follows Lean's and thus does not follow [semantic
versioning][1]. Instead, a new version of Nerodia is released for each minor
Lean version (i.e., Nerodia 4.X for Lean 4.X.Y-Z), usually once per month.

[1]: https://semver.org/

Nerodia publishes a Git branch for each Lean minor version and a Git tag for
each Lean patch version. The branch is named `release/lean-v4.X` for minor
version X and the tag is named `lean-v4.X.Y` for patch version Y. For example,
Nerodia has a `release/lean-v4.33` branch and `lean-v4.33.0` and `lean-v4.33.1`
tags for the Lean v4.33.X stable releases.

If Nerodia needs to update a release, it will be listed here as a new patch
version (e.g., Nerodia 4.33.1), and the corresponding Git branch along with
Git tag for the latest Lean stable release will be updated to point to it.
For example, if Nerodia 4.33.1 was released and the latest Lean stable is Lean
4.33.1, the `release/lean-v4.33` branch and `lean-v4.33.1` tag will be updated,
but the `lean-v4.33.0` tag will not.

It is recommended that users {ref "require-nerodia"}[depend] on the
`release/lean-v4.X` branch for the minimum combination of Nerodia and Lean
toolchain they support. Nerodia aims to be generally forward-compatible in
its API, and an old version of Nerodia is often compatible with multiple newer
toolchains.

# Nerodia 4.34.0
%%%
tag := "4.34.0"
%%%

- Introduction of this reference manual.

- *Breaking change:* {lean}`Py.Raw` has been removed from the public API as part
of a refactor of {lean}`Typing` and the `⦂` operator. It is now internal and most
of its uses should be replaced with {lean}`PyObject`.

- *Breaking change:* {lean}`OfPyArg`, {lean}`MkPyResult`, {lean}`MkCPyResult`,
and {lean}`PyCResultIO` have been removed from the public API and are now internal.
However, the compiler {ref "type-conversions"}[type conversions] they provide
are still part of the public surface and are still stable in this version.

- `ByteArray` produces `bytes` as a result type
  (see {ref "type-conversions"}[type conversions]).

- Added {name}`Option` {ref "type-conversions"}[type conversions].

- Added {lean}`PyBool` and {lean}`Bool` {ref "type-conversions"}[type conversions].

- API for calling 0-arity and 1-arity Python functions
({lean}`PyObject.call0`, {lean}`PyObject.call1`).

- Python integer support for fixed-width Lean integer types
({tech}`IntX`, {tech}`UIntX`).

# Nerodia 4.33.0
%%%
tag := "4.33.0"
%%%

- Initial release.
