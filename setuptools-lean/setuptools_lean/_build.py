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
from setuptools.command.build_ext import build_ext, get_abi3_suffix
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
    ["lake", "script", "run", "nerodia/buildExt", *modules],
    stdout=subprocess.PIPE, env=env,
  )
  r.check_returncode()
  return [json.loads(line) for line in r.stdout.decode().splitlines()]

def finalize_lean(dist: Distribution):
  """Entry point for setuptools via `finalize_distribution_options`."""
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
  # Nerodia extensions use the Python Limited API (abi3).
  # Set the wheel tag so a single wheel works across Python versions.
  # TODO: Determine the minimum abi3 version from Lake instead of hardcoding.
  bdist_wheel = dist.get_option_dict("bdist_wheel")
  bdist_wheel.setdefault("py_limited_api", ("setuptools-lean", "cp313"))

class build_lean(Command):
  """Build Lean/Nerodia Python extension modules.

  Runs Lake to generate and compile the Python extension, then
  bundles it up into a distributable package (or editable install).
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
      mod_pkg = config['name']
      generated = not os.path.isdir(mod_pkg)

      # Determine target directory for the package.
      # For generated packages in editable mode, install directly to site-packages
      # since setuptools' editable mechanism won't find generated packages.
      # This assumes the build runs with the target venv's Python (i.e., no
      # build isolation), which is the case for editable installs.
      if generated and build_ext_cmd.inplace:
        pkg_dir = os.path.join(sysconfig.get_path('purelib'), mod_pkg)
      elif not build_ext_cmd.inplace:
        pkg_dir = os.path.join(build_ext_cmd.build_lib, mod_pkg)
      else:
        pkg_dir = mod_pkg
      os.makedirs(pkg_dir, exist_ok=True)

      # Generate `__init__.py` if no source directory exists
      if generated:
        with as_file(files('setuptools_lean').joinpath('data/init_stub')) as init_stub:
          shutil.copy2(init_stub, os.path.join(pkg_dir, "__init__.py"))

      # Create type stubs
      shutil.copy2(config['pyi'], os.path.join(pkg_dir, "__init__.pyi"))
      open(os.path.join(pkg_dir, "_lean.pyi"), 'w').close()
      open(os.path.join(pkg_dir, "py.typed"), 'w').close()

      # Copy the extension's shared library
      abi3_suffix = get_abi3_suffix()
      if generated and build_ext_cmd.inplace:
        ext_suffix = abi3_suffix or sysconfig.get_config_var('EXT_SUFFIX')
        assert isinstance(ext_suffix, str)
        ext_path = os.path.join(pkg_dir, f"_lean{ext_suffix}")
      else:
        ext_path = build_ext_cmd.get_ext_fullpath(f"{mod_pkg}._lean")
        if abi3_suffix is not None:
          so_ext = sysconfig.get_config_var('EXT_SUFFIX')
          assert isinstance(so_ext, str)
          ext_path = ext_path[:-len(so_ext)] + abi3_suffix
      os.makedirs(os.path.dirname(ext_path), exist_ok=True)
      shutil.copy2(config['lib'], ext_path)

      # Bundle Lean shared libs (skip for user-provided editable installs)
      if generated or not build_ext_cmd.inplace:
        libs_dir = os.path.join(os.path.dirname(ext_path), ".libs")
        os.makedirs(libs_dir, exist_ok=True)
        for lib in config['libs']:
          shutil.copy2(lib, libs_dir)


class LeanBuildExt(build_ext):
  """Thin shim that delegates Lean extension building to ``build_lean``."""

  def run(self):
    super().run()
    self.run_command("build_lean")
