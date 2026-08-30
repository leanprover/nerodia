/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
-/
module
public import VersoManual.InlineLean
import all VersoManual.InlineLean

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

namespace NerodiaManual

open Lean.Syntax Verso.Doc.Elab SubVerso.Highlighting in
@[inline]
public meta nonrec def toHighlightedLeanBlock
  (shouldShow : Bool) (hls : Highlighted) (str: StrLit) : DocElabM Term
:= do toHighlightedLeanBlock shouldShow hls str

open Lean Verso.Doc.Elab in
/--
Elaborates the provided Lean command in the context of the current Verso module.
Unlike `lean`, this allows a header which is parsed and skipped.
-/
@[code_block]
public meta def leanModule : CodeBlockExpanderOf LeanBlockConfig
  | config, str => do
    let input := str.getString
    let s := ParseImports.main input (ParseImports.whitespace input {})
    let some startPos := str.raw.getPos?
      | throwErrorAt str "Expected a string literal with source positions, \
        but it has none"
    let endPos := ⟨startPos.byteIdx + s.pos.byteIdx⟩
    if let some err := s.error? then
      throwErrorAt (.ofRange ⟨startPos, endPos⟩) err
    else
      let info := .synthetic endPos (str.raw.getTailPos?.getD endPos)
      elabCommands config (Syntax.mkStrLit "" info) toHighlightedLeanBlock
