import os
import sys
import json
import sysconfig

free_threaded = bool(sysconfig.get_config_var('Py_GIL_DISABLED'))

libdir = sysconfig.get_config_var('LIBDIR')
ldlib = sysconfig.get_config_var('LDLIBRARY')
ldversion = sysconfig.get_config_var('LDVERSION')

# A static CPython's LDLIBRARY is an archive (libpython{LDVERSION}.a).
# Py_ENABLE_SHARED is absent on Windows, which always ships python3.dll.
is_shared = (sys.platform == 'win32' or
  bool(sysconfig.get_config_var('Py_ENABLE_SHARED')))

if ldlib and libdir and sys.platform != 'win32':
  # POSIX: use the versioned library in LIBDIR.
  # PY3LIBRARY (the stable ABI library) is unusable on modern Linux
  # (empty stub, see python/cpython#104612) and absent on macOS.
  lib3_name = lib3x_name = f'python{ldversion}'
  if sys.platform == 'darwin' and sysconfig.get_config_var('PYTHONFRAMEWORK'):
    # macOS framework build: LDLIBRARY is the framework binary (e.g.,
    # Python.framework/Versions/3.14/Python), not a dylib.
    # LIBDIR contains a libpython{LDVERSION}.dylib symlink to it.
    lib3_path = lib3x_path = os.path.join(libdir, f'libpython{ldversion}.dylib')
  else:
    lib3_path = lib3x_path = os.path.join(libdir, ldlib)
elif sys.platform == 'win32':
  # Windows: python3.dll (the stable ABI DLL) lives in the install root.
  # Use sys.base_prefix (not sys.executable) so this works inside a
  # virtualenv, where sys.executable points to the venv's Scripts/ dir.
  lib3_name = 'python3'
  lib3x_name = f"python{sys.version_info.major}{sys.version_info.minor}"
  libdir = sys.base_prefix
  lib3_path = os.path.join(libdir, 'python3.dll')
  lib3x_path = os.path.join(libdir, f'{lib3x_name}.dll')
else:
  raise RuntimeError(f"unsupported platform: {sys.platform}")

if not os.path.exists(lib3_path):
  raise FileNotFoundError(f"expected Python library at {lib3_path}")
if not os.path.exists(lib3x_path):
  raise FileNotFoundError(f"expected Python library at {lib3x_path}")

# include has the Python C API headers; platinclude has pyconfig.h
# both matter if CPython is built with differing --prefix and --exec-prefix
include = sysconfig.get_path('include')
platinclude = sysconfig.get_path('platinclude')
include_dirs = [include] if include == platinclude else [include, platinclude]

cfg = {
  "exe": sys.executable,
  "version": sys.version,
  "hexVersion": sys.hexversion,
  "freeThreaded": free_threaded,
  "includeDirs": include_dirs,
  "libDir": libdir,
  "lib3": (lib3_name, lib3_path),
  "lib3x": (lib3x_name, lib3x_path),
  "isShared": is_shared,
}

json.dump(cfg, sys.stdout)
