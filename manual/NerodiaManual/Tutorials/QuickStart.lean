/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/

import VersoManual
import NerodiaManual.Meta.Toml
import NerodiaManual.Meta.LeanModule
import Nerodia

open Verso.Genre Manual

namespace NerodiaManual

#doc (Manual) "Quick Start" =>
%%%
tag := "quick-start"
%%%

Nerodia allows you to write native Python modules in pure Lean.
To demonstrate this, the following steps adapt the `string_sum` example from
PyO3's [README](https://github.com/PyO3/pyo3#using-rust-from-python).

First, create a new Lake package and add Nerodia as a dependency.
This can be done by running `lake new string_sum lib.toml` and then updating
`string_sum/lakefile.toml` to the following:

*lakefile.toml*
```toml
# The package name need not match anything
name = "lean-string-sum"
defaultTargets = ["StringSum"]

[[lean_lib]]
name = "StringSum"

[[require]]
name = "nerodia"
scope = "leanprover"
```

After adding Nerodia as a dependency, run `lake update nerodia` from within
the package's directory (e.g., `string_sum`). Once complete, the next step is
to define the Python interface in Lean. As an example, open `StringSum.lean`
and add the following code. (If you used `lake new`, you can also delete the
`StringSum` directory as it will not be needed.)

*StringSum.lean*
```leanModule -keep
module
import Nerodia
open scoped Nerodia

-- Names the module. Unlike PyO3, this does not
-- need to be synchronized with any other setting.
py_module "string_sum"

/-- Formats the sum of two numbers as a string. -/
-- camelCase name for Lean with a snake_case name for Python
@[py_module_fn "sum_as_string"]
def sumAsString (a b : Nat) : String :=
  toString (a + b)
```

This defines a Python module named `string_sum` that has a single module
function named `sum_as_string` that is implemented by our `sumAsString` Lean
function. Nerodia will intelligently infer the Python type signature
`(a: int, b: int, /) -> str` from the function's Lean type and perform the
necessary conversions between Python objects and Lean objects to link them.

You can then build and distribute this module as a Python package with minimal
configuration via the [`setuptools-lean`][1] Python package, which integrates
Nerodia into Python's  [`setuptools`][2] build system.  To do so, create a
[`pyproject.toml`][3] that configures `setuptools-lean` as  an additional
build system requirement that targets the Lean module.

[1]: https://github.com/leanprover/setuptools-lean
[2]: https://github.com/pypa/setuptools
[3]: https://packaging.python.org/en/latest/specifications/pyproject-toml/

*pyproject.toml*
```toml
[project]
# The project name need not match anything
name = "py-string-sum"
version = "1.0.0"
requires-python = ">=3.14"

[build-system]
requires = ["setuptools", "setuptools-lean"]
build-backend = "setuptools.build_meta"

[tool.setuptools]
# setuptools-lean will generate a Python package for us.
# Without this field, setuptools may assume Lean libraries are Python packages.
# Python packages of your own can be added to this list.
packages = []

[[tool.setuptools-lean.ext-modules]]
lean-module = "StringSum"
```

This Python package can then be built and run like any other.
For instance, with the [`uv`](https://github.com/astral-sh/uv) package manager,
a single `uv run python` is all it takes to start using the module.

```
# From within the `string_sum` package directory
$ uv run python
>>> import string_sum
>>> string_sum.sum_as_string(5, 20)
'25'
>>> string_sum.sum_as_string.__doc__
'Formats the sum of two numbers as a string.'
```

In addition, Nerodia automatically generates type stubs for the module and
`setuptools-lean` locates them where they need to be so that type checkers and
editors will pick them up. Thus, editing a Python module that imports a Nerodia
module will provide all the rich type information and docstrings users might
expect from regular Python code.
