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
from typing import TypedDict

class NerodiaConfig(TypedDict):
  name: str
  c: str
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
  """Run Lake to generate Lean/Nerodia Python extension modules."""

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

    if self.distribution.ext_modules is None:
      self.distribution.ext_modules = []

    for nerodia in configs:
      mod = nerodia['name']
      # Create `__init__` stub with module definitions and the docstring
      shutil.copy2(nerodia['pyi'], os.path.join(mod, "__init__.pyi"))
      # Create empty `_lean` stub to handle `from ._lean` resolution in `__init__`
      open(os.path.join(mod, "_lean.pyi"), 'w').close()
      # Create Python extension
      self.distribution.ext_modules.append(
        setuptools.Extension(f"{mod}._lean",
          sources=[nerodia['c']],
          include_dirs=nerodia['includeDirs'],
          library_dirs=nerodia['libDirs'],
          libraries=nerodia['libs'],
          extra_objects=nerodia['objs'],
          extra_compile_args=["-std=c17"],
        )
      )

class LeanBuildExt(build_ext):
  """Build extension modules with Lean FFI compatibility.

  Runs ``build_lean`` to generate extensions, then overrides compiler
  selection for Lean FFI compatibility. Lean is built with a Unix-style
  toolchain (MinGW/clang on Windows), so its headers and libraries are
  incompatible with MSVC. This replaces setuptools' compiler with a
  UnixCCompiler to ensure compatibility.
  """

  def run(self):
    self.run_command("build_lean")
    # build_lean populates dist.ext_modules after finalize_options ran,
    # so re-read extensions and initialize setuptools' internal state.
    self.extensions = self.distribution.ext_modules or []
    self.check_extensions_list(self.extensions)
    for ext in self.extensions:
      ext._full_name = self.get_ext_fullname(ext.name)
      ext._links_to_dynamic = False
      ext._needs_stub = False
      ext._file_name = self.get_ext_filename(ext._full_name)
      self.ext_map[ext._full_name] = ext
      self.ext_map[ext._full_name.split('.')[-1]] = ext
    super().run()

  def build_extensions(self):
    from setuptools._distutils.unixccompiler import UnixCCompiler
    cc = os.environ.get("CC", "cc")
    cxx = os.environ.get("CXX", "c++")
    # macOS requires -undefined dynamic_lookup so that Python C API symbols
    # (provided by the interpreter at load time) don't cause link errors.
    if sys.platform == "darwin":
      linker_so = f"{cc} -shared -undefined dynamic_lookup"
    else:
      linker_so = f"{cc} -shared"
    self.compiler = UnixCCompiler()
    self.compiler.set_executables(
      compiler=cc,
      compiler_so=f"{cc} -fPIC",
      compiler_cxx=cxx,
      linker_so=linker_so,
      linker_exe=cc,
    )
    # Re-apply command-level settings that build_ext.run()
    # applied to the old compiler before calling build_extensions().
    if self.include_dirs:
      self.compiler.set_include_dirs(self.include_dirs)
    if self.define:
      for name, value in self.define:
        self.compiler.define_macro(name, value)
    if self.undef:
      for macro in self.undef:
        self.compiler.undefine_macro(macro)
    if self.libraries:
      self.compiler.set_libraries(self.libraries)
    if self.library_dirs:
      self.compiler.set_library_dirs(self.library_dirs)
    if self.rpath:
      self.compiler.set_runtime_library_dirs(self.rpath)
    if self.link_objects:
      self.compiler.set_link_objects(self.link_objects)
    super().build_extensions()
