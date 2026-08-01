# Nerodia

Nerodia is a library for Lean/Python FFI inspired by [PyO3](https://github.com/PyO3/pyo3). It utilizes Lake, Lean's build system, to provide seeamless intergation. The name of the library comes from the genus _Nerodia_, a type of water snake. That is, a snake you would find in a lake.

**Important:** Nerodia is still a **work-in-progress** and currently has a very limited API. It is released to the public primarily as a proof-of-concept and to obtain feedback on its design and build process.

## A Python Package in Pure Lean

Nerodia allows you to write native Python modules in pure Lean. To demonstrate this, the following steps adapt the `string_sum` example from PyO3's [README](https://github.com/PyO3/pyo3#using-rust-from-python).

First, create a new Lake package and add Nerodia as a dependency. This can be done by running  `lake new string_sum lib.toml` and then updating `string_sum/lakefile.toml` to the following:

**lakefile.toml**
```toml
name = "string-sum"
defaultTargets = ["StringSum"]

[[lean_lib]]
name = "StringSum"

[[require]]
name = "nerodia"
sope = "leanprover"
```

After setting up Nerodia, the next step is to define the Python interface in Lean. As an example, open `StringSum.lean` and add the following code. (If you used `lake new`, you can also delete the `StringSum` directory as it will not be needed.)

**StringSum.lean**
```lean
module
import Nerodia
open scoped Nerodia

-- Names the module. Unlike pyO3, this does not
-- needed to be synchronized with any other setting.
py_module "string_sum"

/-- Formats the sum of two numbers as a string. -/
-- Uses a camelCase name for Lean, but a snake_case mame for Python
@[py_module_fn "sum_as_string"]
def sumAsString (a b : Nat) : String :=
  toString (a + b)
```

This defines a Python module name `string_sum` that has a single module function named `sum_as_string` that is implemented by our `sumAsString` Lean function. Nerodia will intellegently infer the Python type signature `(a: int, b: int, /) -> str` from the function's Lean type and perform the necessary conversions between Python objects and Lean objects to link them.

You can then build and distribute this module as a Python package with minimal configuration via the [`setuptools-lean`](https://github.com/leanprover/setuptools-lean) Python package, which integrates Nerodia into Python's [`setuptools`](https://github.com/pypa/setuptools) build system. To do so, create a [`pyproject.toml`](https://packaging.python.org/en/latest/specifications/pyproject-toml/) that configures `setuptools-lean` as an additional build system requirement that targets the Lean module.

**pyproject.toml**
```toml
[project]
name = "sum-string"
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

This Python package can then built and run like any other. For instance, with the [`uv`](https://github.com/astral-sh/uv) package manager, a single `uv run python` is all it takes to start using the module.

```shell
$ uv run python
>>> import string_sum
>>> string_sum.sum_as_string(5, 20)
'25'
>>> string_sum.sum_as_string.__doc__
'Formats the sum of two numbers as a string.'
```

In addition, Nerodia automatically generates type stubs for the module and `setuptools-lean` locates them where they need to be so that type checkers and editors will pick them up. Thus, editing a Python module that imports a Nerodia module will provide all the rich type information and doscstrings users might expect from regular Python code.
