# Building and checking the frozen packages

This repository targets Lean 4.35.0. Install its standard toolchain with elan, then run commands from this checkout. Python 3 is required for the vendored gate. Package dependencies use local relative paths; the pinned lean-sail source overlay must be materialized before Lake resolves those paths. No private Git remote is required for the upstream fetch.

The model contains 1,481 modules. Full builds belong on a machine with sufficient memory. The release measurement is performed on GB10 with the native Lake scheduler, a shared 110 GiB memory ceiling, swap disabled and `-M12288` on Lean processes. The model's reviewed elaboration options are retained in its Lake configuration. `LEAN_NUM_THREADS` controls Lake scheduling; it is separate from the model compiler's `-j1` option.

This fallback is source-only. No prebuilt model, runtime or native cache is redistributed while upstream runtime permissions remain unresolved. Model-generated C contains runtime specialization bodies, so omitting the separate runtime archive does not make a model cache runtime-free. Candidate archives and cache tooling remain private pending permission review.

The cold-build entrypoint invokes the verified fetch before its first Lake update and includes fetch time. To materialize the runtime separately, run (POSIX sh, Git and one supported SHA256 utility):

```sh
./scripts/fetch-lean-sail
```

The clean GB10 fallback test took about 465 seconds including fetch, passed all four fresh owned-package gates and reproduced all 1,481 canonical model hashes. This is a measured preparation result, not a general build-time promise or publication approval. See [source-fetch-cold.json](../evidence/source-fetch-cold.json) for the measured source/configuration identity and separate final-wiring tests; [Getting started](../README.md#getting-started) records the source/mirror and unconfirmed Software Heritage provenance boundary.

Check source identity before building:

```sh
python3 tools/check-model-reproduction.py
```

Build and gate the runtime, then the complete model:

```sh
(cd vendor/lean-sail && lake update && lake run gate)
(cd model && lake update && lake run gate)
python3 tools/check-model-reproduction.py --artifacts
```

Each fresh gate cleans that package's owned build products, disables artifact restoration, builds its complete default target, scans sources, reads full-private declaration bodies and checks the transitive axiom closure. Gate receipts live in that package's `.lake/diagnostics/gate-*/gate.json`. Incremental diagnostic receipts do not attest a fresh build.

The opted-in timing policy allows at most 600 seconds for the complete fresh build and gate, and 300 seconds for configuration preflight, source scanning and raw-body checking together. It never omits declarations to meet those limits. A receipt that exceeds either limit fails. Configurations without the opt-in retain the legacy combined gate budget; the release package explicitly opts in.

The observer package has its own default build and gate:

```sh
(cd observers && lake update && lake run gate)
```

The enclosing package also has a gate. Its default target builds the import entry point and a separate `RuntimeChecks` root containing all four runtime regression modules. Applications import only `ArmCert`. Its successful receipt does not replace checking each package's complete owned default target. The source-only fallback cold test passed all four fresh owned-package gates and every canonical model artifact hash in465.128seconds including fetch; see [source-fetch-cold.json](../evidence/source-fetch-cold.json) for its input-equivalence/final-wiring qualification. Earlier full-vendor cold-build and precommit receipts remain historical evidence. The public fetch layout supports native Lake; separate private materialized-source Git inputs passed fleet validation. Final source-export/patch review, hygiene, CI rollout and owner approval remain separate steps. All prebuilt model/runtime/native caches stay private; no download endpoint is enabled.

The runtime uses uniform standard options without a monitor plugin. Historical artifact reconstruction and its limitations are documented in [runtime reproduction](RUNTIME-REPRODUCTION.md). Model artifacts must match every SHA256 in `model/SOURCES.json`. Assertion diagnostic strings retained in the model are inert data; see [limitations](LIMITATIONS.md).
