import Lake
open Lake DSL

package «lean-sail» where
  moreLeanArgs := #["-j1", "-M12288", "-DElab.async=false"]

require «lean-buildtools» from "../lean-buildtools"

@[default_target]
lean_lib Sail where
  roots := #[`Sail]
  globs := #[.one `Sail, .submodules `Sail]

@[default_target]
lean_lib SailTests where
  roots := #[]
  globs := #[.submodules `SailTests]

script gate args do
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["run", "lean-buildtools/gate"] ++ args.toArray
  }
  child.wait
