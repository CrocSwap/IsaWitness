# IsaWitness v1: trust base

A result proved over IsaWitness depends on the items below. Each is listed with the evidence the release supplies for it.

| Trusted item | What you rely on | Evidence in this release |
|---|---|---|
| Arm architecture sources (2023-03) | That the source pseudocode describes the architecture | None. Known issues are listed in [LIMITATIONS](LIMITATIONS.md) |
| Sail and its Lean backend | That the translation preserves the pseudocode's meaning | Finite Isla cross-validation, with mismatches and partials kept visible |
| `lean-sail` runtime | The runtime definitions, plus the recorded choices and corrections | Pinned upstream commit, patch series and per-file SHA256 |
| Lean 4.35.0 kernel | Proof checking | Standard. Only `propext`, `Classical.choice` and `Quot.sound` are allowed |
| Build recipe | That the artifacts come from the sources | Canonical artifact hashes and [REPRODUCIBILITY](REPRODUCIBILITY.md) |

## Proof checking
- Each owned package has a fresh gate that does three things:
  - builds the package's full default target with artifact restoration disabled;
  - reads every declaration body, including private ones;
  - checks the transitive axiom closure.
- Native evaluation (`native_decide`, `ofReduceBool`, `implemented_by` under proofs) is not used as a proof method.
- The import-only wrapper's gate does not substitute for the model, runtime and observer gates.

## Tool boundary
- The gate's artifact reader, `AxiomGraph.lean`, is tool-only. The gate enforces that it stays outside every proof closure.
- The reader memory-maps artifacts using unsafe reads. Run it only on outputs of your own fresh build, never on downloaded or untrusted `.olean` files.

## Model, consumer and hardware
- Model witnesses show that a constructed state is satisfiable. They do not attest that the state matches a real target.
- Each consumer must state, explicitly:
  - the processor's identification and feature values;
  - entry controls, address translation and memory mappings;
  - caller contracts and run-preservation conditions.
- Hardware timing, speculation and physical deployment are not established by this release.
