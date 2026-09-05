
/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen, Mac Malone
-/
module

public meta import VersoManual.InlineLean.IO
public meta import NerodiaManual.Meta.Toml

open Verso Doc Elab Genre.Manual Html Code InlineLean IOExample
open SubVerso.Highlighting Highlighted
open Lean Elab

open Lean.Elab.Term (mkFreshIdent)

namespace NerodiaManual

structure ExampleContext where
  lean? : Option (Name × Ident) := none
  inputFiles : Array (System.FilePath × StrLit) := #[]
  deriving Repr

meta initialize exampleCtx : EnvExtension (Option ExampleContext) ←
  Lean.registerEnvExtension (pure none)

meta def querySubVersoExtractMod : IO System.FilePath := do
  let out ← IO.Process.output {cmd := "lake", args := #["query", "subverso-extract-mod"]}
  if out.exitCode != 0 then
    throw <| .userError s!"\
      When running 'lake query subverso-extract-mod', \
        the exit code was {out.exitCode}\n\
      Stderr:\n{out.stderr}\n\n\
      Stdout:\n{out.stdout}\n\n"
  let some extractMod := out.stdout.splitOn "\n" |>.head?
    | throw <| .userError "No executable path found"
  IO.FS.realPath extractMod

meta initialize subversoExtractModRef : IO.Ref (Option System.FilePath) ←
  IO.mkRef none

meta def getSubVersoExtractMod : IO System.FilePath := do
  if let some path ← subversoExtractModRef.get then
    return path
  if let some path ← unsafe subversoExtractModRef.take then
    subversoExtractModRef.set (some path)
    return path
  let path ← querySubVersoExtractMod
  subversoExtractModRef.set (some path)
  return path

meta def check
  (modName : Name) (inputFiles : Array (System.FilePath × StrLit))
: DocElabM Highlighted := IO.FS.withTempDir fun dirname => do
  -- Write example
  let toolchain : String ← IO.FS.readFile "lean-toolchain"
  IO.FS.writeFile (dirname / "lean-toolchain") toolchain
  for (f, i) in inputFiles do
    IO.FS.writeFile (dirname / f) i.getString
  -- Build example
  let out ← IO.Process.output {
    cmd := "lake", args := #["build"],
    cwd := some dirname
  }
  if out.exitCode != 0 then
    throwError m!"\
      When running 'lake build' in {dirname}, \
        the exit code was {out.exitCode}\n\
      Stderr:\n{out.stderr}\n\n\
      Stdout:\n{out.stdout}\n\n"
  -- Extract highlighted Lean
  let jsonFile := s!"{modName}.json"
  let extractMod ← getSubVersoExtractMod
  let out ← IO.Process.output {
    cmd := extractMod.toString
    args := #[modName.toString, jsonFile]
    cwd := some dirname
  }
  if out.exitCode != 0 then
    throwError m!"\
      When running '{extractMod} {modName} {jsonFile}' in {dirname}, \
        the exit code was {out.exitCode}\n\
      Stderr:\n{out.stderr}\n\n\
      Stdout:\n{out.stdout}\n\n"
  let json ← IO.FS.readFile (dirname / jsonFile)
  let json ← IO.ofExcept <| Json.parse json
  match SubVerso.Module.Module.fromJson? json with
  | .ok v => return v.items.foldl (init := .empty) fun hl item => hl ++ item.code
  | .error e => throwError m!"\
    Failed to deserialized JSON output as highlighted Lean code. Error: \
      {indentD e}\n\
    JSON: {json}"

meta def startExample : DocElabM Unit := do
  match exampleCtx.getState (← getEnv) with
  | some _ => throwError "Can't initialize - already in a context"
  | none => modifyEnv fun env => exampleCtx.setState env (some {})

meta def endExample (body : Term) : DocElabM Term := do
  match exampleCtx.getState (← getEnv) with
  | none => throwErrorAt body "Can't end example - never started"
  | some {lean?, inputFiles, ..} => do
    modifyEnv fun env =>
      exampleCtx.setState env none
    let some (modName, hlVar) := lean?
      | throwError "No code specified"
    let hlLean ← check modName inputFiles
    `(let $hlVar : Highlighted := $(quote hlLean)
      $body)

meta def saveInputFile (name : System.FilePath) (src : StrLit) : DocElabM Unit := do
  match exampleCtx.getState (← getEnv) with
  | none => throwError "Can't save file - not in an Nerodia example"
  | some st =>
    modifyEnv fun env => exampleCtx.setState env <|
      some {st with inputFiles := st.inputFiles.push (name, src)}

meta def saveLeanFile (name : System.FilePath) (src : StrLit) : DocElabM Ident := do
  match exampleCtx.getState (← getEnv) with
  | none => throwError "Can't set Lean code - not in an Nerodia example"
  | some st =>
    if st.lean?.isSome then
      throwError "Code already specified"
    let hlVar ← mkFreshIdent (← getRef)
    let modName := (name.withExtension "").components.foldl .str .anonymous
    modifyEnv fun env => exampleCtx.setState env <| some {st with
      lean? := some (modName, hlVar),
      inputFiles := st.inputFiles.push (name, src)
    }
    return hlVar

@[code_block]
public meta def inputToml : CodeBlockExpanderOf FileConfig
  | opts, str => do
    saveInputFile opts.name str
    if opts.show then
      let hl ← tomlContent str
      ``(Block.other (Block.toml $(quote hl)) #[Block.code $(quote str.getString)])
    else
      ``(Block.empty)

@[code_block]
public meta def inputLean : CodeBlockExpanderOf FileConfig
  | opts, str => do
    let x ← saveLeanFile opts.name str
    if opts.show then
      let range := Syntax.getRange? str
      let range := range.map (← getFileMap).utf8RangeToLspRange
      ``(Block.other (Block.lean $x (some $(quote (← getFileName))) $(quote range)) #[Block.code $(quote str.getString)])
    else
      ``(Block.empty)

@[directive]
public meta def nerodiaExample : DirectiveExpanderOf Unit
 | (), blocks => do
    startExample
    let body ← blocks.mapM elabBlock
    let body ← ``(Verso.Doc.Block.concat #[$body,*])
    endExample body
