# setuptools-lean

The `setuptools-lean` package provides a [setuptools](https://github.com/pypa/setuptools) plugin for building and bundling Python extensions written in Lean. It uses [Nerodia](https://github.com/leanprover/nerodia) as its Lean backend.

## Quick Start

Python modules are configured on the Lean side through Nerodia. For example,
the Lean definition of the Python module `mymodule` would look something like this:

**MyModule.lean**
```lean
import Nerodia

open Nerodia

py_module "mymodule"
```

This module can then be bundled into a Python package with the following configuration:

**pyproject.toml**
```toml
[project]
name = "mypackage"
requires-python = ">=3.13"

[build-system]
requires = ["setuptools", "setuptools-lean"]
build-backend = "setuptools.build_meta"

[[tool.setuptools-lean.ext-modules]]
lean-module = "MyModule"
```

This package can then be install locally via `pip install .`, and the installed Python extension imported via `import mymodule`. If you are using [uv](https://github.com/astral-sh/uv), running Python code that imports `mymodule` is as simple as running `uv run importer.py` in the same directory as the Python extension (no manual install necessary).