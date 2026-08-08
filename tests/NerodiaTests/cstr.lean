/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Claude Code
-/
import Nerodia.Compiler.Emit.C

/-!
# C String Literals

This test verifies the C string literals the Nerodia compiler generates.
Each expected output below is the C source text, not a Lean string literal.
-/

open Nerodia.Compiler

/-- info: "" -/
#guard_msgs in #eval IO.println <| cstr ""

/-- info: "Add two integers using Lean." -/
#guard_msgs in #eval IO.println <| cstr "Add two integers using Lean."

/-! ## Escapes

Control characters use octals: a C hex escape consumes every hex digit that
follows it, so `\x0b` before a letter is a different (often invalid) character.
-/

/-- info: "a\013beta" -/
#guard_msgs in #eval IO.println <| cstr "a\x0Bbeta"

/-- info: "docs.\014deadbeef" -/
#guard_msgs in #eval IO.println <| cstr "docs.\x0Cdeadbeef"

/-- info: "\177" -/
#guard_msgs in #eval IO.println <| cstr "\x7F"

/-- info: "line\r\nfields\tapart" -/
#guard_msgs in #eval IO.println <| cstr "line\r\nfields\tapart"

/-- info: "a \"quote\", a \\, a \? (trigraph)" -/
#guard_msgs in #eval IO.println <| cstr "a \"quote\", a \\, a ? (trigraph)"

/-! ## Non-ASCII

Escaped byte-by-byte, so the bytes of the literal do not depend on
the character sets the C compiler is configured with.
-/

/-- info: "caf\303\251, \316\273, \360\237\220\215" -/
#guard_msgs in #eval IO.println <| cstr "café, λ, 🐍"
