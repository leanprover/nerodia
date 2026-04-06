# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code
import os
import sys
import json
import subprocess
import setuptools
from setuptools.command.build_ext import build_ext

r=subprocess.run(
  ["lake", "query", "--json", "Test:static", "Nerodia:static"],
  stdout=subprocess.PIPE, env=dict(os.environ, PYTHON3=sys.executable)
)
r.check_returncode()
static_libs = [json.loads(ln) for ln in r.stdout.decode().splitlines()]

r = subprocess.run(
  ["lean", "--print-prefix"],
  stdout=subprocess.PIPE
)
r.check_returncode()
lean_sysroot = r.stdout.decode().strip()


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
    self.compiler = UnixCCompiler()
    self.compiler.set_executables(
      compiler=cc,
      compiler_so=cc,
      compiler_cxx=cxx,
      linker_so=f"{cc} -shared",
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
        setuptools.Extension("testmodule",
            sources=["module.c"],
            include_dirs=[f"{lean_sysroot}/include"],
            library_dirs=[f"{lean_sysroot}/lib/lean"],
            libraries=["leanshared"],
            extra_objects=static_libs,
            extra_compile_args=["-std=c17"],
        )
    ]
)
