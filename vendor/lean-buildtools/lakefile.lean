import Lake
open System Lake DSL

package «lean-buildtools» where
  version := v!"0.3.0"
  moreLeanArgs := #["-M12288"]

-- Scripts are deliberately always-run actions, never cached gate receipts.
private def tool (command : String) (args : List String) : ScriptM UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #[(__dir__ / "tools.py").toString, command,
      "--project", (← getRootPackage).dir.toString] ++ args.toArray
  }
  child.wait

/-- Fresh default build, own source policy and transitive raw-body axiom check. -/
script gate args do tool "gate" args

/-- Read-only source scan; does not claim compiled axiom coverage. -/
script «source-scan» args do tool "source-scan" args

/-- Native Lake metadata for separate executable compiler environments. -/
script «gate-contexts» args do
  match args with
  | [output] =>
    let pkg ← getRootPackage
    let roots := pkg.leanExes.map fun exe => exe.root.name.toString
    IO.FS.writeFile output (Lean.toJson roots).pretty
    return 0
  | _ =>
    IO.eprintln "usage: lake run lean-buildtools/gate-contexts OUTPUT.json"
    return 1
