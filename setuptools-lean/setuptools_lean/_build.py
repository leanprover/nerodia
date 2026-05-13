# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code
import os
import sys
import json
import shutil
import tomllib
import subprocess
import setuptools
from pathlib import Path
from setuptools.command.build_ext import build_ext
from setuptools.dist import Distribution
from setuptools._distutils.core import Command
from typing import TypedDict, cast

class NerodiaConfig(TypedDict):
  name: str
  c: str
  o: str
  pyi: str
  includeDirs: list[str]
  libDirs: list[str]
  libs: list[str]
  objs: list[str]

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

    for nerodia in configs:
      mod = nerodia['name']
      # Create `__init__` stub with module definitions and the docstring
      shutil.copy2(nerodia['pyi'], os.path.join(mod, "__init__.pyi"))
      # Create empty `_lean` stub to handle `from ._lean` resolution in `__init__`
      open(os.path.join(mod, "_lean.pyi"), 'w').close()
      # Build the the extension's shared library
      self._build_extension(nerodia, build_ext_cmd)

  def _build_extension(self, config: NerodiaConfig, build_ext_cmd: build_ext):
    cc = os.environ.get("CC", "cc")
    mod = config['name']
    ext_name = f"{mod}._lean"
    output_path = build_ext_cmd.get_ext_fullpath(ext_name)

    # Link
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    link_cmd = [cc, '-shared']
    # macOS requires -undefined dynamic_lookup so that Python C API symbols
    # (provided by the interpreter at load time) don't cause link errors.
    if sys.platform == 'darwin':
      link_cmd.extend(['-undefined', 'dynamic_lookup'])
    link_cmd.extend(config['objs'])
    for d in config['libDirs']:
      link_cmd.extend(['-L', d])
    for lib in config['libs']:
      link_cmd.extend(['-l', lib])
    # On Windows/MinGW and Cygwin, all symbols in shared libraries must be
    # resolved at link time, so we must link against the Python library.
    # We also add build_ext's library dirs which include Python's lib path.
    if sys.platform in ('win32', 'cygwin'):
      for d in (build_ext_cmd.library_dirs or []):
        link_cmd.extend(['-L', d])
      for lib in build_ext_cmd.get_libraries(setuptools.Extension(ext_name, sources=[])):
        link_cmd.extend(['-l', lib])
    link_cmd.extend(['-o', output_path])
    subprocess.run(link_cmd, check=True)

class LeanBuildExt(build_ext):
  """Thin shim that delegates Lean extension building to ``build_lean``."""

  def run(self):
    super().run()
    self.run_command("build_lean")
