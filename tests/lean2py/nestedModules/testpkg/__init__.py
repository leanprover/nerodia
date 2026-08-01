# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code

"""A package provided by the project which contains a Lean extension."""

from .ext import greet

hello = greet()
