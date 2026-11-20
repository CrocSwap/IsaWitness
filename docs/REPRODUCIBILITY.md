# Reproducing the canonical v9 model

[REVISION.json](../model/REVISION.json) identifies the exact proof commit. [CANONICAL-SOURCES.sha256](../model/CANONICAL-SOURCES.sha256) records the raw bytes of 1,560 `ArmFull` and 11 `Sail` modules, including the two root modules. The default Lake build compiles the pinned inventory and its dependencies.

1. Use Lean 4.35.0 as specified by `lean-toolchain`.
2. Run `./scripts/fetch-lean-sail` to verify the upstream Git identity, replay the source edits and verify the resulting runtime.
3. Run `python3 tools/check-model-reproduction.py` to check canonical source hashes and source inventory.
4. Run `lake build` with the package settings. The model and runtime use `-j1` and Lean's default asynchronous elaboration, as in the reviewed v9 build. Changing elaboration settings can change generated matcher names and private declarations.
5. Run `python3 tools/check-model-reproduction.py --built` to check the source pins and the entire built `.olean` inventory. Use [the fresh gate recipe](BUILD.md) when checking axioms and build provenance.

Lake records package metadata in its artifacts. A per-module driver can produce different artifact bytes from the same model sources. A cross-recipe comparison should inspect the kernel declarations and their types and values in addition to source hashes. The v9 manifest pins sources and the built check verifies artifact inventory. The reviewed comparison of the legacy and public v9 header builds records the accepted kernel residuals. [Equivalence report](../evidence/model-equivalence/README.md)

The preceding publication pinned SHA256 values for artifacts from a 1,481-module model. Its receipt and historical measurements remain available. [Previous model receipt](../evidence/v1-frozen-model-sources.json) · [Historical cold build](../evidence/source-fetch-cold.json)
