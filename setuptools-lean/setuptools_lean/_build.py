# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code
import os
import sys
import json
import shutil
import sysconfig
import tomllib
import subprocess
from pathlib import Path
from setuptools.dist import Distribution
from setuptools.command.build_ext import build_ext
from setuptools._distutils.core import Command
from importlib.resources import files, as_file
from typing import TypedDict, cast

class NerodiaConfig(TypedDict):
  name: str
  c: str
  o: str
  pyi: str
  lib: str
  libs: list[str]

def run_lake(modules: list[str]) -> list[NerodiaConfig]:
  """
  Generates extension configurations for the given modules using Lake.
  Returns one configuration per module.
  """
  env = dict(os.environ, PYTHON3=sys.executable)
  if sys.platform == 'darwin':
    # Override Lean's default MACOSX_DEPLOYMENT_TARGET (99.0) with the value
    # Python was built with so the extension's platform tag matches Python's.
    env['MACOSX_DEPLOYMENT_TARGET'] = sysconfig.get_config_var('MACOSX_DEPLOYMENT_TARGET')
  r = subprocess.run(
    ["lake", "script", "run", "nerodia/genExt", *modules],
    stdout=subprocess.PIPE, env=env,
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
      generated = not os.path.isdir(mod)

      # Determine target directory for the package.
      # For generated packages in editable mode, install directly to site-packages
      # since setuptools' editable mechanism won't find generated packages.
      if generated and build_ext_cmd.inplace:
        pkg_dir = os.path.join(sysconfig.get_path('purelib'), mod)
      elif not build_ext_cmd.inplace:
        pkg_dir = os.path.join(build_ext_cmd.build_lib, mod)
      else:
        pkg_dir = mod
      os.makedirs(pkg_dir, exist_ok=True)

      # Generate __init__.py if no source directory exists
      if generated:
        with as_file(files('setuptools_lean').joinpath('data/init_stub')) as init_stub:
          shutil.copy2(init_stub, os.path.join(pkg_dir, "__init__.py"))

      # Create type stubs
      shutil.copy2(config['pyi'], os.path.join(pkg_dir, "__init__.pyi"))
      open(os.path.join(pkg_dir, "_lean.pyi"), 'w').close()
      open(os.path.join(pkg_dir, "py.typed"), 'w').close()

      # Copy the extension's shared library
      if generated and build_ext_cmd.inplace:
        ext_path = os.path.join(
          pkg_dir, f"_lean{sysconfig.get_config_var('EXT_SUFFIX')}")
      else:
        ext_path = build_ext_cmd.get_ext_fullpath(f"{mod}._lean")
      os.makedirs(os.path.dirname(ext_path), exist_ok=True)
      shutil.copy2(config['lib'], ext_path)

      # Bundle Lean shared libs (skip for user-provided editable installs)
      if not (not generated and build_ext_cmd.inplace):
        libs_dir = os.path.join(os.path.dirname(ext_path), ".libs")
        os.makedirs(libs_dir, exist_ok=True)
        for lib in config['libs']:
          shutil.copy2(lib, libs_dir)


class LeanBuildExt(build_ext):
  """Thin shim that delegates Lean extension building to ``build_lean``."""

  def run(self):
    super().run()
    self.run_command("build_lean")
