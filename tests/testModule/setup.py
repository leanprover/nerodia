import os
import sys
import json
import subprocess
import setuptools

r=subprocess.run(
  ["lake", "query", "--json", "Test:static", "Nerodia:static"],
  stdout=subprocess.PIPE, env=dict(os.environ, PYTHON3=sys.executable)
)
r.check_returncode()
static_libs=[json.loads(ln) for ln in r.stdout.decode().splitlines()]

r=subprocess.run(
  ["lean", "--print-prefix"],
  stdout=subprocess.PIPE
)
r.check_returncode()
lean_sysroot=r.stdout.decode().strip()

setuptools.setup(ext_modules=[
  setuptools.Extension("testmodule",
    sources=["module.c"],
    include_dirs=[f"{lean_sysroot}/include"],
    library_dirs=[f"{lean_sysroot}/lib/lean"],
    libraries = ["leanshared"],
    extra_objects = static_libs,
  )
])
