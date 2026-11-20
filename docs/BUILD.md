# Build and validate IsaWitness

Install the Lean 4.35.0 toolchain, Git and Python 3.11 or later. IsaWitness contains 1,560 `ArmFull` modules, 11 canonical `Sail` modules and 22 ObsGen modules. Lake resolves dependencies from paths inside the checkout.

Run these commands from the repository root to materialize the runtime and check all 1,571 canonical source hashes.

```sh
./scripts/fetch-lean-sail
python3 tools/check-model-reproduction.py
lake update
lake build
```

The cold-build entry point fetches the source, disables Lake artifact restoration, builds and gates all four packages, then confirms that every canonical model and runtime module produced an `.olean`.

```sh
bash tools/run-cold-build.sh
```

Start with a clean checkout for a cold measurement. Set `ISAWITNESS_LEAN_SAIL_SOURCE` to a local pinned Git mirror when needed. The gate records its receipts under `.lake/validation/` by default. `LEAN_NUM_THREADS` controls Lake scheduling. The model and runtime packages set a separate per-process Lean thread and memory limit in their Lake configuration. Use a host sized for the number of concurrent builds.

## Package gates

The complete check runs the package gates in this order.

```sh
(cd vendor/lean-sail && lake update && lake run gate)
(cd model && lake update && lake run gate)
(cd observers && lake update && lake run gate)
lake update && lake run gate
python3 tools/check-model-reproduction.py --built
```

Each gate cleans the owned package's build products, builds the complete default target, scans sources and checks the transitive axiom closure of the owned declarations, including private bodies. The root package builds both the `ArmCert` import entry point and `RuntimeChecks`, which imports the four runtime regression modules. The timing policy allows 600 seconds for the complete fresh run and a separate 300-second limit for package preflight, source scanning and raw-body checking.

The previous source-only release preparation completed the four gates in about 465 seconds, including fetch. That measurement used the preceding 1,481-module model and runtime wiring. [Historical timing](../evidence/source-fetch-cold.json) · [Current provider status](PROVIDER-STATUS.md)
