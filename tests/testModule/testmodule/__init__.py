# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code
import os
import sys
import subprocess

# On Windows 3.8+, PATH doesn't affect DLL resolution for extensions.
# Add Lean's shared library directory so libleanshared.dll is found.
if sys.platform == "win32":
    r = subprocess.run(["lean", "--print-prefix"], stdout=subprocess.PIPE)
    lean_sysroot = r.stdout.decode().strip()
    r.check_returncode()
    os.add_dll_directory(os.path.join(lean_sysroot, "bin"))

from ._lean import *
from ._lean import __doc__