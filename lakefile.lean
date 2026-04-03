import Lake
open System Lake DSL
open Lean (Json ToJson FromJson toJson fromJson?)

package nerodia where
  leanOptions := #[⟨`doc.verso, true⟩]

/-! ## Python -/

structure PyConfig where
  version : String
  hexVersion : String
  libName : String
  libPath : FilePath
  includeDir : FilePath
  deriving ToJson, FromJson

instance : QueryText PyConfig := ⟨(toJson · |>.compress)⟩

input_file pyconfigSrc where
  text := true
  path := "pyconfig.py"

target pyconfig : PyConfig := do
  (← pyconfigSrc.fetch).mapM fun srcFile => do
    let out ← captureProc {cmd := "python3", args := #[srcFile.toString]}
    match Json.parse out >>= fromJson? with
    | .ok cfg =>
      setTrace <| .ofHash
        (pureHash cfg.hexVersion) s!"pyconfig: {cfg.version}"
      return cfg
    | .error e =>
      error s!"configuration script produced unexpect output; {e}:\n{out}"

target libpython3 : Dynlib := do
  return (← pyconfig.fetch).map (sync := true) fun py =>
    {name := py.libName, path := py.libPath}

/-! ## Nerodia FFI -/

input_file nerodia.c where
  text := true
  path := "ffi" / "nerodia.c"

target nerodia.o pkg : FilePath := do
  let cJob ← nerodia.c.fetch
  (← pyconfig.fetch).bindM fun py => do
    let oFile := pkg.irDir / "c" / "nerodia.o"
    let weakArgs := #[
      s!"-I{py.includeDir}",
      s!"-I{← getLeanIncludeDir}"
    ]
    let traceArgs := pkg.buildType.leancArgs ++ #[
      s!"-DPy_LIMITED_API={py.hexVersion}",
      "-fPIC", "-std=c17", "-Wall"
    ]
    let cc := (← IO.getEnv "CC").getD "cc"
    buildO oFile cJob weakArgs traceArgs cc getLeanTrace

target libnerodiaffi pkg : FilePath := do
  let libName := pkg.staticLibDir / nameToStaticLib "nerodiaffi"
  let oJob ← nerodia.o.fetch
  buildStaticLib libName #[oJob]

/-! ## Nerodia Lean -/

@[default_target]
lean_lib Nerodia where
  defaultFacets := #[LeanLib.sharedFacet]
  moreLinkObjs := #[libnerodiaffi]
  moreLinkLibs := #[libpython3]

lean_lib NerodiaTests where
  srcDir := "tests"
  globs := #[`NerodiaTests.+]
  precompileModules := true

lean_exe testExe where
  srcDir := "tests"

@[test_driver]
script test do
  runBuild do
    let libJob ← NerodiaTests.fetch
    let exeJob ← testExe.fetch
    withRegisterJob "testExe test" do
      libJob.bindM fun _ =>
      exeJob.mapM fun exeFile => do
        let out ← captureProc {cmd := exeFile.toString}
        unless out == "hello" do
          error s!"incorrect output: expected \"hello\", got {out.quote}"
  return 0
