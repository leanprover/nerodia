/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Nerodia.Compiler.ModuleConfig.Basic

open System (FilePath)

namespace Nerodia

public def writePyiFile (path : FilePath) (mod : ModuleDef) : IO Unit := do
  let pyi ← IO.FS.Handle.mk path .write
  pyi.putStr "# Nerodia compiler output\n"
  if let some doc := mod.doc? then
    pyi.putStr doc.quote
    pyi.putStr "\n"
  for m in mod.attrs do
    pyi.putStr s!"\n{m.name}: {m.ty}"
    if let some doc := m.doc? then
      pyi.putStr "\n"
      pyi.putStr doc.quote
  pyi.putStr "\n"
  for m in mod.methods do
    pyi.putStr "\ndef "
    pyi.putStr m.name
    pyi.putStr m.pySig
    if let some doc := m.doc? then
      pyi.putStr ":\n  "
      pyi.putStr doc.quote
      pyi.putStr "\n  ..."
    else
      pyi.putStr ": ..."
  pyi.putStr "\n"
