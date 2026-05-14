# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code
import os
import sys
import types
import subprocess

# On Windows 3.8+, PATH doesn't affect DLL resolution for extensions.
# Add the directory containing Lean's shared libraries so they are found.
if sys.platform == "win32":
    libs_dir = os.path.join(os.path.dirname(__file__), ".libs")
    if os.path.isdir(libs_dir):
        os.add_dll_directory(libs_dir)
    else:
        r = subprocess.run(["lean", "--print-prefix"], stdout=subprocess.PIPE)
        lean_sysroot = r.stdout.decode().strip()
        r.check_returncode()
        os.add_dll_directory(os.path.join(lean_sysroot, "bin"))
        del r, lean_sysroot
    del libs_dir

from ._lean import *
from ._lean import __doc__

# Use this module instead of `_lean` for re-exported definitions
for obj in list(vars().values()):
    if hasattr(obj, '__module__') and not isinstance(obj, types.ModuleType):
        obj.__module__ = __name__
del obj

# Clear imports
del os, sys, types, subprocess, _lean
