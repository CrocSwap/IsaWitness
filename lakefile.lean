import Lake
open Lake DSL

package ArmCert where
  version := v!"0.1.0"
  moreLeanArgs := #["-M12288"]

require «lean-buildtools» from "vendor/lean-buildtools"
require ArmFull from "model"
require ArmCertObservers from "observers"

@[default_target]
lean_lib ArmCert where
  roots := #[`ArmCert, `RuntimeChecks]

script gate args do
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["run", "lean-buildtools/gate"] ++ args.toArray
  }
  child.wait
