/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Compiler.Data.ModuleConfig.Basic

open System (FilePath)

namespace Nerodia.Compiler

public def writePyiFile (path : FilePath) (mod : ModuleDef) : IO Unit := do
  let pyi ← IO.FS.Handle.mk path .write
  pyi.putStr "# Nerodia compiler output\n"
  if let some doc := mod.doc? then
    pyi.putStr doc.quote
    pyi.putStr "\n"
  pyi.putStr "\n\
    from types import *\n\
    from typing import *\n\
    from collections.abc import *\n"
  for df in mod.attrs do
    pyi.putStr "\n"
    pyi.putStr df.name
    if let some ty := df.ty? then
      pyi.putStr ": "
      pyi.putStr ty
    else
      pyi.putStr " = ..."
    if let some doc := df.doc? then
      pyi.putStr "\n"
      pyi.putStr doc.quote
  pyi.putStr "\n"
  for df in mod.methods do
    pyi.putStr "\ndef "
    pyi.putStr df.name
    pyi.putStr df.pySig
    if let some doc := df.doc? then
      pyi.putStr ":\n  "
      pyi.putStr doc.quote
      pyi.putStr "\n  ..."
    else
      pyi.putStr ": ..."
  pyi.putStr "\n"
