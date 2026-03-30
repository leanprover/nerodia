import Lake
open System Lake DSL
open Lean (Json ToJson FromJson toJson fromJson?)

package nerodia where
  leanOptions := #[⟨`doc.verso, true⟩]

/-! ## Python -/

structure PyConfig where
  hexVersion : String
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
    | .ok cfg => return cfg
    | .error e => error s!"configuration script produced unexpect output; {e}:\n{out}"

target libpython3 : Dynlib := do
  return (← pyconfig.fetch).map (sync := true) fun py =>
    {name := "python3", path := py.libPath}

/-! ## Nerodia FFI -/

input_file nerodia.c where
  text := true
  path := "ffi" / "nerodia.c"

target nerodia.o pkg : FilePath := do
  (← pyconfig.fetch).bindM fun py => do
    let oFile := pkg.irDir / "c" / "nerodia.o"
    let weakArgs := #[s!"-I{py.includeDir}", s!"-I{← getLeanIncludeDir}"]
    let traceArgs := pkg.buildType.leancArgs ++ #[
      s!"-DPy_LIMITED_API={py.hexVersion}",
      "-fPIC", "-std=c17", "-Wall"
    ]
    let cc := (← IO.getEnv "CC").getD "cc"
    buildO oFile (← nerodia.c.fetch) weakArgs traceArgs cc getLeanTrace

target libnerodiaffi pkg : FilePath := do
  let libName := pkg.staticLibDir / nameToStaticLib "nerodiaffi"
  let oJob ← nerodia.o.fetch
  buildStaticLib libName #[oJob]

/-! ## Nerodia Lean -/

lean_lib Nerodia where
  moreLinkObjs := #[libnerodiaffi]
  moreLinkLibs := #[libpython3]

@[test_driver]
lean_lib NerodiaTests where
  globs := #[`NerodiaTests.+]
  precompileModules := true
