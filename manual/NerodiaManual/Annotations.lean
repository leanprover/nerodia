/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
module
public import VersoManual
import all Nerodia.Compiler.Meta.Commands
import all Nerodia.Compiler.Meta.Attributes
public import Nerodia

open Nerodia
open Verso.Genre Manual InlineLean

namespace NerodiaManual

#doc (Manual) "Annotations" =>
%%%
tag := "annotations"
htmlSplit := .never
%%%

A Python module is defined in Nerodia by annotating Lean modules with metadata
via commands and attributes. The Nerodia compiler reads this metdata and uses it
to generate a Python extension with the desired properties.

A Lean module must first use `py_module` to declare itself as a Python module
before any of the other annotations can be used.

# `py_module`
%%%
tag := "py_module"
%%%

```lean
/-- My awesome Python moudule. -/
py_module "awesome"
```

{includeDocstring  Nerodia.Compiler.pyModuleCmd}

# `@[py_module_fn]`
%%%
tag := "py_module_fn"
%%%

```lean
/-- Formats the sum of two numbers as a string. -/
@[py_module_fn "sum_as_string"]
def sumAsString (a b : Nat) : String :=
  toString (a + b)
```

{includeDocstring  Nerodia.Compiler.py_module_fn}

# `@[py_module_attr]`
%%%
tag := "py_module_attr"
%%%

```lean
/-- A magic number for the module. -/
@[py_module_attr] def magic := 42
```

{includeDocstring  Nerodia.Compiler.py_module_attr}

# `@[py_module_init]`
%%%
tag := "py_module_init"
%%%

```lean
@[py_module_init]
def winOnlyAttr : PyModuleInit := .ofPyIO fun mod => do
  if System.Platform.isWindows then
    mod.addByString "isWindows" (← getPyTrue)
```

{includeDocstring  Nerodia.Compiler.py_module_init}
