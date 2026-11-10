import Lake
open Lake DSL
package ArmCertObservers where
  moreLeanArgs := #["-j1", "-M12288", "--tstack=400000"]
require ArmFull from "../model"
require «lean-sail» from "../vendor/lean-sail"
require «lean-buildtools» from "../vendor/lean-buildtools"
@[default_target]
lean_lib ObsGen where
  globs := #[.one `ObsGen, .submodules `ObsGen]
script gate args do
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["run", "lean-buildtools/gate"] ++ args.toArray
  }
  child.wait
