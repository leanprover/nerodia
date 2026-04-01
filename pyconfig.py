import os
import sys
import json
import sysconfig

libdir = sysconfig.get_config_var('LIBDIR')
py3lib = sysconfig.get_config_var('PY3LIBRARY')

if py3lib and libdir:
  # POSIX (Linux, etc.): PY3LIBRARY is the stable ABI shared library
  libPath = os.path.join(libdir, py3lib)
elif sys.platform == 'win32':
  # Windows: python3.dll is next to the interpreter.
  # Must be checked before the POSIX fallback because recent CPython
  # sets LIBDIR on Windows (pointing to the import library directory).
  libPath = os.path.join(os.path.dirname(sys.executable), 'python3.dll')
elif sys.platform == 'darwin' and sysconfig.get_config_var('PYTHONFRAMEWORK'):
  # macOS framework build: the library is the framework binary itself.
  # LDLIBRARY is a relative path (e.g., Python.framework/Versions/3.13/Python)
  # that must be joined with PYTHONFRAMEWORKPREFIX, not LIBDIR.
  fwdir = sysconfig.get_config_var('PYTHONFRAMEWORKPREFIX')
  ldlib = sysconfig.get_config_var('LDLIBRARY')
  if not fwdir or not ldlib:
    raise RuntimeError("expected PYTHONFRAMEWORKPREFIX and LDLIBRARY on darwin framework build")
  libPath = os.path.join(fwdir, ldlib)
elif libdir:
  # POSIX fallback (macOS non-framework, debug builds, AIX, etc.):
  # PY3LIBRARY is not set; fall back to LDLIBRARY in LIBDIR
  ldlib = sysconfig.get_config_var('LDLIBRARY')
  if not ldlib:
    raise RuntimeError(f"expected LDLIBRARY to be set on {sys.platform}")
  libPath = os.path.join(libdir, ldlib)
else:
  raise RuntimeError(f"unsupported platform: {sys.platform}")

if not os.path.exists(libPath):
  raise FileNotFoundError(f"expected Python library at {libPath}")

cfg = {
  "hexVersion": hex(sys.hexversion),
  "includeDir": sysconfig.get_path('include'),
  "libPath": libPath,
}

json.dump(cfg, sys.stdout)
