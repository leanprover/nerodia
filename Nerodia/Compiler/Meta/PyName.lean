/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Lean.Data.Trie
public import Lean.Meta.Basic
public import Lean.Elab.Command

namespace Nerodia.Compiler

/--
Returns whether the string is a reserved Python keyword (as of [v3.14][1]).

[1]: https://docs.python.org/3.14/reference/lexical_analysis.html#keywords
-/
def isPyKeyword (s : String.Slice) : Bool :=
  trie.matchPrefix s.str s.startInclusive.offset s.endExclusive.offset.byteIdx
    |>.any fun n => s.startInclusive.offset.byteIdx + n == s.endExclusive.offset.byteIdx
where
  trie : Lean.Data.Trie Nat :=
    keywords.foldl (fun t kw => t.insert kw kw.utf8ByteSize) .empty
  keywords := #[
    "False",      "await",      "else",       "import",     "pass",
    "None",       "break",      "except",     "in",         "raise",
    "True",       "class",      "finally",    "is",         "return",
    "and",        "continue",   "for",        "lambda",     "try",
    "as",         "def",        "from",       "nonlocal",   "while",
    "assert",     "del",        "global",     "not",        "with",
    "async",      "elif",       "if",         "or",         "yield",
  ]

@[inline] def isAsciiPyStart (c : Char) : Bool :=
    c == '_' || c.isAlpha

@[inline] def isAsciiPyContinue (c : Char) : Bool :=
    c == '_' || c.isAlphanum

def takeAsciiPyName (s : String.Slice) (h : s.startPos ≠ s.endPos) : String.Slice :=
  let p := s.startPos
  if isAsciiPyStart (p.get h) then
    s.sliceFrom (p.next h |>.skipWhile isAsciiPyContinue)
  else
    s

/--
Returns whether the string is a valid ASCII Python [name][1].

[1]: https://docs.python.org/3.14/reference/lexical_analysis.html#names-identifiers-and-keywords
-/
def isAsciiPyName (s : String.Slice) : Bool :=
  if h : s.startPos = s.endPos then
    false
  else takeAsciiPyName s h |>.isEmpty

/-- Returns whether the string is pure ASCII (e.g., no Unicode characters). -/
def isAscii (s : String.Slice) : Bool :=
  s.all (Char.val · ≤ 127)

@[inline] def validatePyName? (name : String.Slice) : Option String := do
  unless isAscii name do
    return s!"non-ASCII names are not supported"
  unless isAsciiPyName name do
    return s!"not a valid Python name"
  if isPyKeyword name then
    return s!"reserved Python keyword"
  none

open Lean

@[inline] def mkPyName (name : Name) : Except String String := do
  match name with
  | .str _ name =>
    match validatePyName? name with
    | some e => throw s!"'{name}': {e}"
    | none => return name
  | _ => throw s!"'{privateToUserName name}': \
    Lean name does not end with a string"

public def mkPyArgName (name : Name) (i : Nat) : MetaM String := do
  if name.isInternalOrNum then
    return if i == 0 then "_" else s!"_{i}"
  else
    match mkPyName name with
    | .ok name => return name
    | .error e => throwError s!"Invalid argument name {e}"

public def mkPyDeclName (name : Name) (override? : Option StrLit) : CoreM String := do
  if let some override := override? then
    withRef override do
    let name := override.getString
    match validatePyName? name with
    | some e => throwError s!"Invalid declaration name '{name}': {e}"
    | none => return name
  else
    match mkPyName name with
    | .ok name => return name
    | .error e => throwError s!"Invalid declaration name {e}"

open Elab Command in
public def mkPyModName (name : StrLit) : CommandElabM String := withRef name do
  let name := name.getString
  for p in name.split '.' do
    if let some e := validatePyName? p then
      throwError s!"Invalid module name '{p}': {e}"
  return name
