/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Compiler.Meta.Commands
public import Nerodia.Compiler.Meta.Attributes
public import Nerodia.Compiler.Meta.Extension

/-!
# Compiler Meta

These modules define the Nerodia metaprograms used to annotate Lean modules
with Python module metadata. This metadata is then processed by the Nerodia
compiler to generate extension files for Python.

When using Nerodia via the standard `import Nerodia`, these modules are
transitively included via a `meta import`.
-/
