module
import Nerodia
open scoped Nerodia

-- Names the module. Unlike pyO3, this does not
-- needed to be synchronized with any other setting.
py_module "string_sum"

/-- Formats the sum of two numbers as a string. -/
-- Uses a camelCase name for Lean, but a snake_case mame for Python
@[py_module_fn "sum_as_string"]
def sumAsString (a b : Nat) : String :=
  toString (a + b)
