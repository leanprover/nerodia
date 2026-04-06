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
  # Windows: python3.dll (the stable ABI DLL) lives in the install root.
  # Use sys.base_prefix (not sys.executable) so this works inside a
  # virtualenv, where sys.executable points to the venv's Scripts/ dir.
  libName = 'python3'
  libPath = os.path.join(sys.base_prefix, 'python3.dll')
else:
  raise RuntimeError(f"unsupported platform: {sys.platform}")

if not os.path.exists(libPath):
  raise FileNotFoundError(f"expected Python library at {libPath}")

# include has the Python C API headers; platinclude has pyconfig.h
# both matter if CPython is built with differing --prefix and --exec-prefix
include = sysconfig.get_path('include')
platinclude = sysconfig.get_path('platinclude')
includeDirs = [include] if include == platinclude else [include, platinclude]

cfg = {
  "version": sys.version,
  "hexVersion": sys.hexversion,
  "libName": libName,
  "includeDirs": includeDirs,
  "libPath": libPath,
}

json.dump(cfg, sys.stdout)
