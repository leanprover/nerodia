# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code
import os
import sys
import types
import subprocess

# On Windows 3.8+, PATH doesn't affect DLL resolution for extensions.
# Add Lean's shared library directory so libleanshared.dll is found.
if sys.platform == "win32":
    r = subprocess.run(["lean", "--print-prefix"], stdout=subprocess.PIPE)
    lean_sysroot = r.stdout.decode().strip()
    r.check_returncode()
    os.add_dll_directory(os.path.join(lean_sysroot, "bin"))
    del r, lean_sysroot

from ._lean import *
from ._lean import __doc__

# Use this module instead of `_lean` for re-exported definitions
for obj in list(vars().values()):
    if hasattr(obj, '__module__') and not isinstance(obj, types.ModuleType):
        obj.__module__ = __name__
del obj

# Clear imports
del os, sys, types, subprocess, _lean
