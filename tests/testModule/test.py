# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone

import testmodule

# TODO: Set `__all__` in `__init__.py` and check it
exports = [x for x in dir(testmodule) if not x.startswith('__')]
expected = ["greet", "greetUser", "greeting", "greeting_for", "setUser"]
assert exports == expected, exports

assert testmodule.__doc__ == "A Lean-to-Python test module."

assert testmodule.greet() == "Hello!"

assert testmodule.greet.__doc__ == "Return a standard greeting."

assert testmodule.greeting == "Hello!"

assert testmodule.greeting_for('Bob') == "Hello, Bob!"

assert testmodule.greeting_for.__doc__ == "Return a greeting."

assert testmodule.greetUser() == "Hello, anonymous!"
assert testmodule.setUser('Bob') is None
assert testmodule.greetUser() == "Hello, Bob!"

assert testmodule.setUser.__doc__ == "Sets the current user."
assert testmodule.greetUser.__doc__ == "Returns a greeting for the current user."

try:
  testmodule.greet("a") # type: ignore[ty:too-many-positional-arguments]
  raise AssertionError('expected TypeError')
except TypeError as e:
  assert str(e) == "testmodule.greet() takes no arguments (1 given)"

try:
  testmodule.greeting_for(0) # type: ignore[ty:invalid-argument-type]
  raise AssertionError('expected TypeError')
except TypeError as e:
  assert str(e) == "testmodule.greeting_for() argument 1 must be str"

try:
  testmodule.greeting_for("a", "b") # type: ignore[ty:too-many-positional-arguments]
  raise AssertionError('expected TypeError')
except TypeError as e:
  assert str(e) == "testmodule.greeting_for() takes exactly one argument (2 given)"

try:
  testmodule.greeting_for(s="a") # type: ignore[ty:positional-only-parameter-as-kwarg]
  raise AssertionError('expected TypeError')
except TypeError as e:
  assert str(e) == "testmodule.greeting_for() takes no keyword arguments"
