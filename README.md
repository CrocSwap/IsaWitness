# IsaWitness

This repository assembles a frozen Sail translation of an Arm® architecture model in Lean, together with a selected 771-form instruction inventory, observation equations and qualified cross-validation evidence. It does not establish full instruction equivalence, constant-time behavior, hardware certification or consumer total correctness.

The frozen model's 1,481 artifacts reproduce the canonical hashes after fresh builds and complete raw-body axiom gates. A clean source-only fetch-and-build test on GB10 passed all four owned-package gates in about 465 seconds, including verified runtime materialization. The final fetch wiring has separate integration tests against byte-identical Lean source/package configuration; this is not an exact-final-entrypoint timing claim. Publication still requires owner approval and final source-export review. See the [source-only measurement](evidence/source-fetch-cold.json), [provider status](docs/PROVIDER-STATUS.md), [build instructions](docs/BUILD.md), [evidence](evidence/README.md) and [limitations](docs/LIMITATIONS.md).

## Getting started

From an approved source checkout, fetch and verify the pinned runtime **before** Lake resolves local path dependencies:

```sh
./scripts/fetch-lean-sail
lake update
lake build
```

For full fresh validation, follow [the build instructions](docs/BUILD.md), which gate each owned package and check every model artifact hash.

The fetch step needs POSIX `sh`, Git, and one of `sha256sum`, `shasum -a 256`, or `openssl dgst -sha256`. It verifies the exact upstream commit and tree, the ordered patch series, every resulting source/configuration SHA256 and the complete file set. Only `UPSTREAM.json`, patches and the first-party `AbstractReal`/`AbstractRealRat` files are distributed in the runtime directory. Lake still sees the local package ID `lean-sail`. The cold-build entrypoint performs this verified fetch before any Lake update and includes fetch time in the measurement. Package-owned .lake build metadata is outside the source inventory; all extra source/payload files, partial fetches and local edits are refused rather than overwritten.

For a previously obtained Git mirror, use `./scripts/fetch-lean-sail --source /path/to/mirror`; the same commit/tree/file pins remain mandatory. Software Heritage provenance is `swh:1:rev:c816ea7ad03cce98d51acee252540fd4215fede8`, but its read-only revision lookup returned 404 and archive availability is **unconfirmed**. No working archived download or public availability is promised. This fallback is source-only: no prebuilt runtime, model or native cache is redistributed while upstream runtime permissions remain unresolved. Fetch and build locally from source. The clean GB10 measurement took about 465 seconds including fetch (roughly 7.8 minutes); other machines and loads can differ. Cache tooling and candidate archives remain private for later permission review. Run the artifact-reading gate only on your own fresh build outputs, never downloaded or untrusted oleans.

The standard Lake packages under `model/`, `vendor/lean-sail/` and `observers/` use relative dependencies within the materialized checkout. The enclosing Git revision pins the first-party files and overlay metadata; the fetched runtime is pinned by its upstream commit/tree and verified resulting file hashes. The source-only gate implementation is vendored separately from proof modules. Model declarations retain their frozen bytes. The runtime and observer public copies normalize internal labels in comments, with original and public source hashes retained in provenance; their declarations are unchanged.

Generated assertion diagnostics retain 2,244 inert path string literals. They do not read files. The full model reproduces its canonical artifact hashes, and normalization is queued for the [next planned model revision](NEXT-REVISION.md).

The per-form step layer is a planned later addition. Its class and pipeline dependencies are still changing. Value, physical-memory and walk-cleanup layers remain outside this first-release scope.

Arm is a registered trademark of Arm Limited (or its subsidiaries or affiliates) in the US and/or elsewhere. This independent project is not sponsored, endorsed or certified by Arm. The public project name is IsaWitness. Canonical Lean package/module identifiers such as `ArmCert` and `ArmFull` remain unchanged for reproducibility.

First-party material is licensed under Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). Third-party terms remain separate, and the runtime patch-distribution/export review and explicit owner approval remain prerequisites for publication. The confirmed first-party copyright holder is Crocodile Labs Inc. Runtime, model and native caches remain private until runtime permission is resolved.

The artifact reader is tool-only and outside every proof closure, enforced by the gate. Run the gate on your own fresh builds, not as an auditor of downloaded or untrusted `.olean` files; the reader memory-maps artifact regions using unsafe reads.
