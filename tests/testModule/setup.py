# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code
import os
import sys
import json
import shutil
import subprocess
import setuptools
from setuptools.command.build_ext import build_ext
from typing import TypedDict

class NerodiaConfig(TypedDict):
  c: str
  pyi: str
  includeDirs: list[str]
  libDirs: list[str]
  libs: list[str]
  objs: list[str]

r=subprocess.run(
  ["lake", "query", "--json", "+Test:nerodia"],
  stdout=subprocess.PIPE, env=dict(os.environ, PYTHON3=sys.executable)
)
r.check_returncode()
nerodia: NerodiaConfig = json.loads(r.stdout.decode())

mod = "testmodule"
# create `__init__` stub with module definitions and the docstring
shutil.copy2(nerodia['pyi'], os.path.join(mod, "__init__.pyi"))
# create empty `_lean` stub to handle `from ._lean` resolution in `__init__`
open(os.path.join(mod, "_lean.pyi"), 'w').close()

class LeanBuildExt(build_ext):
  """Override compiler selection for Lean FFI compatibility.

  Lean is built with a Unix-style toolchain (MinGW/clang on Windows),
  so its headers and libraries are incompatible with MSVC. This replaces
  setuptools' compiler with a UnixCCompiler to ensure compatibility.
  """

  def build_extensions(self):
    from distutils.unixccompiler import UnixCCompiler
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

setuptools.setup(
    cmdclass={"build_ext": LeanBuildExt},
    ext_modules=[
        setuptools.Extension(f"{mod}._lean",
            sources=[nerodia['c']],
            include_dirs=nerodia['includeDirs'],
            library_dirs=nerodia['libDirs'],
            libraries=nerodia['libs'],
            extra_objects=nerodia['objs'],
            extra_compile_args=["-std=c17"],
        )
    ]
)
