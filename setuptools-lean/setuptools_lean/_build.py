# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code
import os
import sys
import json
import shutil
import tomllib
import subprocess
from pathlib import Path
from setuptools.dist import Distribution
from setuptools.command.build_ext import build_ext
from setuptools._distutils.core import Command
from typing import TypedDict, cast

class NerodiaConfig(TypedDict):
  name: str
  c: str
  o: str
  pyi: str
  lib: str

def run_lake(modules: list[str]) -> list[NerodiaConfig]:
  """
  Generates extension configurations for the given modules using Lake.
  Returns one configuration per module.
  """
  r = subprocess.run(
    ["lake", "script", "run", "nerodia/genExt", *modules],
    stdout=subprocess.PIPE, env=dict(os.environ, PYTHON3=sys.executable),
  )
  r.check_returncode()
  return [json.loads(line) for line in r.stdout.decode().splitlines()]

def finalize_lean(dist: Distribution):
  """setuptools.finalize_distribution_options entry point."""
  pyproject = Path("pyproject.toml")
  if not pyproject.exists():
    return
  with open(pyproject, "rb") as f:
    data = tomllib.load(f)
  ext_modules = data.get("tool", {}).get("setuptools-lean", {}).get("ext-modules")
  if not ext_modules:
    return
  dist.setuptools_lean_modules = ext_modules
  dist.cmdclass.setdefault("build_lean", build_lean)
  dist.cmdclass.setdefault("build_ext", LeanBuildExt)
  # Ensure setuptools treats this as an extension package (needed for wheels).
  dist.has_ext_modules = lambda: True

class build_lean(Command):
  """Build Lean/Nerodia Python extension modules.

  Runs Lake to generate compiled C sources and type stubs, then links
  each extension directly using a Unix-style C compiler.
  """

  description = "build Lean/Nerodia extension modules"
  user_options = []

  def initialize_options(self):
    pass

  def finalize_options(self):
    pass

  def run(self):
    ext_mods = getattr(self.distribution, 'setuptools_lean_modules', None)
    if not ext_mods:
      return

    lean_mods = [m['lean-module'] for m in ext_mods]
    configs = run_lake(lean_mods)

    build_ext_cmd = cast(build_ext, self.get_finalized_command('build_ext'))

    for config in configs:
      mod = config['name']
      # Create `__init__` stub with module definitions and the docstring
      shutil.copy2(config['pyi'], os.path.join(mod, "__init__.pyi"))
      # Create empty `_lean` stub to handle `from ._lean` resolution in `__init__`
      open(os.path.join(mod, "_lean.pyi"), 'w').close()
      # Create the extension's shared library
      ext_path = build_ext_cmd.get_ext_fullpath(f"{mod}._lean")
      os.makedirs(os.path.dirname(ext_path), exist_ok=True)
      shutil.copy2(config['lib'], ext_path)


class LeanBuildExt(build_ext):
  """Thin shim that delegates Lean extension building to ``build_lean``."""

  def run(self):
    super().run()
    self.run_command("build_lean")
