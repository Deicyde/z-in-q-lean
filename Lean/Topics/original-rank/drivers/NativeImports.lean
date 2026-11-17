import Lean

open Lean in
/-- Follow the actual compiled imports of the project, vendored code and Tau Ceti. -/
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let mut pending := args
  let mut seen : Std.HashSet String := {}
  while !pending.isEmpty do
    let raw := pending.head!
    pending := pending.tail!
    if seen.contains raw then continue
    seen := seen.insert raw
    let path ← findOLean raw.toName
    let (md, region) ← readModuleData path
    let deps := md.imports.toList.map fun i => i.module.toString
    IO.println <| String.intercalate "\t" (raw :: path.toString :: deps)
    for dep in deps do
      let root := (dep.splitOn ".").head!
      if ["ZInQKernel","ZInQ","Pkg","TauCeti","Submission","ChallengeDeps"].contains root then
        pending := dep :: pending
    region.free
