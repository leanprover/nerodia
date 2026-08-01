# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code
import testpkg
import testpkg.ext
import testgen.deep

# A generated subpackage of a package provided by the project

assert testpkg.ext.__doc__ == "A Lean extension nested in a package provided by the project."

assert testpkg.ext.greet() == "Hello from testpkg.ext!"

assert testpkg.ext.lean_str == "lean"

assert testpkg.ext.double(21) == 42

# The extension is usable from its parent package's own code
assert testpkg.hello == "Hello from testpkg.ext!"

# The qualified module name reaches the generated diagnostics
try:
  testpkg.ext.double(-1)
  raise AssertionError('expected ValueError')
except ValueError as e:
  assert str(e) == "testpkg.ext.double() argument 1 must be a nonnegative integer, got -1"

# A fully generated qualified package

assert testgen.deep.__doc__ == "A Lean extension in a fully generated qualified package."

assert testgen.deep.greet() == "Hello from testgen.deep!"

assert testgen.deep.answer == 42

# The qualified name survives the extension's re-export into its package
assert testpkg.ext.greet.__module__ == "testpkg.ext"
assert testgen.deep.greet.__module__ == "testgen.deep"
