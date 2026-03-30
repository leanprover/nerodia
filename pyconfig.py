import os
import sys
import json
import sysconfig

libdir = sysconfig.get_config_var('LIBDIR')
py3lib = sysconfig.get_config_var('PY3LIBRARY')

if libdir and py3lib:
  libPath = os.path.join(libdir, py3lib)
else:
  # Windows: python3.dll is next to the interpreter
  libPath = os.path.join(os.path.dirname(sys.executable), 'python3.dll')

cfg = {
  "hexVersion": hex(sys.hexversion),
  "includeDir": sysconfig.get_path('include'),
  "libPath": libPath,
}

json.dump(cfg, sys.stdout)
