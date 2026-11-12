# Reproducing the model bit for bit

IsaWitness pins the model by its exact bytes. A fresh build from the pinned sources must reproduce the canonical SHA256 of all 1,481 `ArmFull` artifacts listed in `model/SOURCES.json`. Downstream proofs depend on generated declaration names, so reproducibility is a correctness requirement, not just a nicety.

## Recipe

1. **Toolchain.** Lean 4.35.0, set in `lean-toolchain`. Use the standard elan toolchain.
2. **Runtime.** Run `./scripts/fetch-lean-sail` before Lake resolves dependencies. It refuses to proceed unless every fetched and patched file matches its pinned hash.
3. **Elaboration options.** Keep them as the packages set them:
   - `model/lakefile.lean` compiles every module with `-j1 -DElab.async=false`.
   - Asynchronous elaboration can renumber auxiliary declarations such as `match_N` matchers and macro hygiene indices. The artifacts then change, and so do the generated names that downstream proofs may mention.
   - Do not override `moreLeanArgs`, and do not set `Elab.async` globally.
4. **Build with Lake.** Lake follows every import form used here: plain `import`, plus 8 `public import` and 15 `public meta import` lines.
   - If you schedule modules yourself (for example, a per-module `lean` driver), your dependency scan must also recognize `public import`, `meta import` and `import all`. Otherwise modules can build out of order against stale artifacts.
   - The regular expression `^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)` is sufficient for these sources.
5. **No restored artifacts.** Lake's artifact cache and restoration must be off for a fresh measurement: `LAKE_ARTIFACT_CACHE=false` and `LAKE_RESTORE_ARTIFACTS=false`, as `tools/run-cold-build.sh` sets them.
6. **Check.** Run:
   ```sh
   python3 tools/check-model-reproduction.py --artifacts
   ```
   It compares every model artifact against `model/SOURCES.json`.

## Receipts
- [complete-cold-build.json](../evidence/complete-cold-build.json), [complete-cold-build-v6.json](../evidence/complete-cold-build-v6.json), [source-fetch-cold.json](../evidence/source-fetch-cold.json): fresh four-package builds and gates that reproduced all 1,481 canonical model hashes.
- Repeated builds with identical options were byte-stable.

## Cross-recipe equivalence

Byte identity holds only within one recipe. A downstream project that compiles the same sources a different way gets different `.olean` bytes. For example, it might invoke `lean` per module from another source root, or use other runtime options. In that case, compare the kernel content instead: every constant's name, type hash and value hash, for every `ArmFull` and `Sail` module.

We ran that comparison against an independent per-module build of identical sources. That build compiled everything, including the runtime, with `-DElab.async=false`. The results:
- **Model:** all 1,481 `ArmFull` modules were identical at the kernel level.
- **Runtime:** 43 constants in four modules differed (`Sail.ArchSem`, `Sail.ArchSemSequential`, `Sail.BitVec`, `Sail.ConcurrencyInterfaceV1`), out of 50,157 constants compared.
  - The differences are only in the numbering of auxiliary `match_N`, `_proof_N` and `_sparseCasesOn_N` declarations, plus the hashes of the definitions that refer to them.
  - The cause is that this package builds the runtime with Lean's default (asynchronous) elaboration.
  - Proofs that mention runtime auxiliary names should use the runtime recipe in `vendor/lean-sail`, or refer to stable lemma names instead.

## What is and is not covered
- The model's canonical hashes cover the 1,481 `ArmFull` artifacts.
- The runtime is accepted by a fresh build plus its axiom gate, using uniform standard options. Some historical runtime artifacts were built under other options. They are documented in [RUNTIME-REPRODUCTION](RUNTIME-REPRODUCTION.md), not reproduced.
- The release measurements were made on Linux AArch64 with Lean 4.35.0. Other platforms are not covered by these receipts.
