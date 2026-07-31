# setuptools-lean package stub
import os
import sys

# On Windows, PATH doesn't affect DLL resolution for extensions.
# Add the directory containing Lean's shared libraries so they are found.
if sys.platform == "win32":
    os.add_dll_directory(os.path.join(os.path.dirname(__file__), "_lean.libs"))

from . import _lean

my_str = _lean.lean_str + 'py'
