import os
import sys
import json
import sysconfig

libdir = sysconfig.get_config_var('LIBDIR')
ldlib = sysconfig.get_config_var('LDLIBRARY')
ldversion = sysconfig.get_config_var('LDVERSION')

if ldlib and libdir and sys.platform != 'win32':
  # POSIX: use the versioned library in LIBDIR.
  # PY3LIBRARY (the stable ABI library) is unusable on modern Linux
  # (empty stub, see python/cpython#104612) and absent on macOS.
  libName = f'python{ldversion}'
  if sys.platform == 'darwin' and sysconfig.get_config_var('PYTHONFRAMEWORK'):
    # macOS framework build: LDLIBRARY is the framework binary (e.g.,
    # Python.framework/Versions/3.13/Python), not a dylib.
    # LIBDIR contains a libpython{LDVERSION}.dylib symlink to it.
    libPath = os.path.join(libdir, f'libpython{ldversion}.dylib')
  else:
    libPath = os.path.join(libdir, ldlib)
elif sys.platform == 'win32':
  # Windows: python3.dll (the stable ABI DLL) is next to the interpreter.
  # Must be checked before the POSIX fallback because recent CPython
  # sets LIBDIR on Windows (pointing to the import library directory).
  libName = 'python3'
  libPath = os.path.join(os.path.dirname(sys.executable), 'python3.dll')
else:
  raise RuntimeError(f"unsupported platform: {sys.platform}")

if not os.path.exists(libPath):
  raise FileNotFoundError(f"expected Python library at {libPath}")

cfg = {
  "version": sys.version,
  "hexVersion": hex(sys.hexversion),
  "libName": libName,
  "includeDir": sysconfig.get_path('include'),
  "libPath": libPath,
}

json.dump(cfg, sys.stdout)
