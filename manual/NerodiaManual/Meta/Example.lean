
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
  files : Array (System.FilePath × String) := #[]
  deriving Repr

@[inline] meta def ExampleContext.empty : ExampleContext := {}

@[inline] meta def ExampleContext.addFile
  (name : System.FilePath) (contents : String) (ctx : ExampleContext)
: ExampleContext := {ctx with files := ctx.files.push (name, contents)}

@[inline] meta def ExampleContext.withTempDir
  [Monad m] [MonadFinally m] [MonadLiftT IO m]
  (ctx : ExampleContext) (x : System.FilePath → m α)
: m α := IO.FS.withTempDir fun dir => do
  for (name, contents) in ctx.files do
    IO.FS.writeFile (dir / name) contents
  x dir

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

meta def buildLean
  (dir : System.FilePath) (modName : Name)
: DocElabM Unit := do
  let out ← IO.Process.output {
    cmd := "lake", args := #["build", modName.toString],
    cwd := some dir
  }
  if out.exitCode != 0 then
    throwError m!"\
      When running 'lake build' in {dir}, \
        the exit code was {out.exitCode}\n\
      Stderr:\n{out.stderr}\n\n\
      Stdout:\n{out.stdout}\n\n"

meta def extractHighlights
  (dir : System.FilePath) (modName : Name)
: DocElabM Highlighted := do
  let jsonFile := s!"{modName}.json"
  let extractMod ← getSubVersoExtractMod
  let out ← IO.Process.output {
    cmd := extractMod.toString
    args := #[modName.toString, jsonFile]
    cwd := some dir
  }
  if out.exitCode != 0 then
    throwError m!"\
      When running '{extractMod} {modName} {jsonFile}' in {dir}, \
        the exit code was {out.exitCode}\n\
      Stderr:\n{out.stderr}\n\n\
      Stdout:\n{out.stdout}\n\n"
  let json ← IO.FS.readFile (dir / jsonFile)
  let json ← IO.ofExcept <| Json.parse json
  match SubVerso.Module.Module.fromJson? json with
  | .ok v => return v.items.foldl (init := .empty) fun hl item => hl ++ item.code
  | .error e => throwError m!"\
    Failed to deserialized JSON output as highlighted Lean code. Error: \
      {indentD e}\n\
    JSON: {json}"

meta register_option skipExamples : Bool := {
  defValue := false
}

meta def getExampleContext : DocElabM ExampleContext := do
  if let some ctx := exampleCtx.getState (← getEnv) then
    return ctx
  else
    let toolchain : String ← IO.FS.readFile "lean-toolchain"
    let ctx := ExampleContext.empty.addFile "lean-toolchain" toolchain
    modifyEnv fun env => exampleCtx.setState env (some ctx)
    return ctx

meta def addExampleFile (name : System.FilePath) (src : StrLit) : DocElabM Unit := do
  let ctx ← getExampleContext
  let ctx := ctx.addFile name src.getString
  modifyEnv fun env => exampleCtx.setState env (some ctx)

meta def saveLeanFile (name : System.FilePath) (src : StrLit) : DocElabM Term := do
  let ctx ← getExampleContext
  let ctx := ctx.addFile name src.getString
  modifyEnv fun env => exampleCtx.setState env (some ctx)
  if skipExamples.get (← getOptions) then
    ``(Block.empty)
  else
    ctx.withTempDir fun dir => do
      let modName := (name.withExtension "").components.foldl .str .anonymous
      buildLean dir modName
      let hl ← extractHighlights dir modName
      return quote hl

@[code_block]
public meta def exampleToml : CodeBlockExpanderOf FileConfig | opts, str => do
  addExampleFile opts.name str
  if opts.show then
    let hl ← tomlContent str
    ``(Block.other (Block.toml $(quote hl)) #[Block.code $(quote str.getString)])
  else
    ``(Block.empty)

@[code_block]
public meta def exampleLean : CodeBlockExpanderOf FileConfig | opts, str => do
  addExampleFile opts.name str
  if skipExamples.get (← getOptions) then
    return ← ``(Block.empty)
  let ctx ← getExampleContext
  ctx.withTempDir fun dir => do
    let modPath := System.FilePath.withExtension opts.name ""
    let modName := modPath.components.foldl .str .anonymous
    buildLean dir modName
    if opts.show then
      let fileName ← getFileName
      let range := str.raw.getRange?.map (← getFileMap).utf8RangeToLspRange
      let x ← extractHighlights dir modName
      let l ← ``(Block.lean $(quote x) (some $(quote fileName)) $(quote range))
      ``(Block.other $l #[Block.code $(quote str.getString)])
    else
      ``(Block.empty)

@[code_block]
public meta def examplePyTest : CodeBlockExpanderOf Unit | _, str => do
  if skipExamples.get (← getOptions) then
    return ← ``(Block.empty)
  let ctx ← getExampleContext
  ctx.withTempDir fun dir => do
    let testFile := dir / "test.py"
    IO.FS.writeFile testFile str.getString
    let out ← IO.Process.output {
      cmd := "uv"
      args := #["run", testFile.toString]
      cwd := some dir
    }
    if out.exitCode != 0 then
      throwError m!"\
        When running 'uv run test.py' in {dir}, \
          the exit code was {out.exitCode}\n\
        Stderr:\n{out.stderr}\n\n\
        Stdout:\n{out.stdout}\n\n"
  ``(Block.empty)
