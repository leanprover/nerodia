# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code

"""
Validates the contents of a test package's source distribution.

Usage: check_sdist.py <project-dir> <out-dir> <expected-file>

Verifies that the sole source distribution in `<out-dir>` contains every path
of the JSON array in `<expected-file>`. Those paths are absolute and lie within
`<project-dir>`, which the distribution was built from; this script puts them
in the form the archive names its members.

They arrive in a file because a package can have more sources than a command
line can hold, and as JSON because a path may contain any character a line
based format would treat as a separator.
"""

import sys
import json
import tarfile
from pathlib import Path, PurePath, PurePosixPath

def contents(sdist: Path) -> set[str]:
  """The archive's files, relative to its `<name>-<version>` root."""
  with tarfile.open(sdist) as tar:
    return {
      PurePosixPath(*PurePosixPath(m.name).parts[1:]).as_posix()
      for m in tar.getmembers() if m.isfile()
    }

def member(path: str, root: PurePath) -> str:
  """How the archive names `path`: relative to `root`, separated by `/`."""
  return PurePath(path).relative_to(root).as_posix()

def main(argv: list[str]) -> int:
  root = PurePath(argv[1])
  out_dir = Path(argv[2])
  paths: list[str] = json.loads(Path(argv[3]).read_text(encoding='utf-8'))
  if not paths:
    # Otherwise a broken path list would make every check pass vacuously.
    print(f"'{argv[3]}' lists no expected paths", file=sys.stderr)
    return 1
  expected = [member(path, root) for path in paths]
  sdists = sorted(out_dir.glob('*.tar.gz'))
  if len(sdists) != 1:
    print(f"expected one source distribution in '{out_dir}', "
      f"found {len(sdists)}", file=sys.stderr)
    return 1
  found = contents(sdists[0])
  missing = [path for path in expected if path not in found]
  if missing:
    print(f"'{sdists[0].name}' is missing sources:", file=sys.stderr)
    for path in missing:
      print(f"  {path}", file=sys.stderr)
    print("it contains:", file=sys.stderr)
    for path in sorted(found):
      print(f"  {path}", file=sys.stderr)
    return 1
  return 0

if __name__ == '__main__':
  sys.exit(main(sys.argv))
