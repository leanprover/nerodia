# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone

import testmodule

assert testmodule.greeting == "Hello!"

assert testmodule.greeting_for('Bob') == "Hello, Bob!"

try:
  testmodule.greeting_for(0)
  raise AssertionError('expected TypeError')
except TypeError as e:
  assert str(e) == "argument must be str"
