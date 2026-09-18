/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Data.HashMap
import VersoManual

import NerodiaManual

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open NerodiaManual

open Verso.Output.Html in
def staticFavicon :=
  {{<link rel="icon" href="static/favicon.ico" type="image/x-icon" />}}

open Verso.Output.Html in
def staticCss :=
  {{<link rel="stylesheet" href="static/extra.css" />}}

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  destination := "_out"
  extraHead := #[staticFavicon, staticCss]
  extraFiles := [("../images", "static"), ("static", "static")]
  logo := some "static/nerodia.svg"

def main (args : List String) : IO UInt32 := do
  Lake.removeDirAllIfExists "_out"
  let rc ← manualMain (%doc NerodiaManual) (config := config) (options := args)
  if rc == 0 then
    IO.FS.createDirAll "_out/doc"
    IO.FS.rename "_out/html-multi" "_out/doc/latest"
  return rc
