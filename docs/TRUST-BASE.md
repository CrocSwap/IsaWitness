# IsaWitness: trust and evidence boundary

> Documentation preparation draft.

## Model and translation

The semantic target is the pinned Sail translation with its recorded runtime declarations and documented source revisions. The architectural model, source-generation process, retained corrections and runtime interpretation form part of the modeling boundary. A kernel-checked result about those definitions is not an independent proof of their correspondence to all implementations of the architecture.

## Proof checking and tools

The proof-axiom policy permits only propext, Classical.choice and Quot.sound. The completed fresh package gates report zero source and axiom errors across all owned declarations. Every included package has its own build and raw-body receipt; the import-only wrapper does not substitute for the model, runtime or observer audits. Native evaluation is not a proof method.

The executable AxiomGraph.lean metadata reader is release-owner approved only as a tool outside every proof closure. The gate enforces that boundary; the proof-axiom allowlist is unchanged. This approval covers that exact artifact reader, and the BuildMonitor plugin remains omitted. IsaWitness is the selected public repository name; canonical Lean package/module identifiers are unchanged. Apache-2.0 applies to first-party code, including vendored first-party lean-buildtools, with copyright held by Crocodile Labs Inc. Third-party runtime permissions, final committed source/cache acceptance and final source-hygiene admission remain separate and pending; no blanket third-party license clearance follows.

Build recipes, Lake setup, the pinned Lean toolchain, exact source identities and gate version 8f6ad8efb8c1931952257b483563b4f7d247d990 are part of reproducibility evidence. Fresh compilation, canonical model artifact matching and axiom audits answer different questions. Historical runtime artifact differences are documented under the uniform public recipe without adding the old monitor plugin.

Run the artifact-reading gate only on artifacts produced by your own fresh build. Do not run it on downloaded or untrusted .olean files: its reader memory-maps artifact regions through unsafe reads. Approval of this executable metadata tool is not permission to import it into proofs or to use it as a proof premise.

The public build path is source-only fetch followed by native Lake builds. Internal fleet registration uses a separate private Git commit that materializes the same hash-verified runtime sources and configuration. The source-only fetch layout does not pass the internal tracked-dependency guard for model, observers and root; the private materialized layout passes all four package checks. The guard is unchanged. These two input layouts do not change the Lean package/module IDs, model declarations or reviewed elaboration options.

No prebuilt runtime, model or native cache is redistributed while upstream runtime permission remains unresolved. Read-only inspection found actual runtime specialization function bodies in model-generated C even though the model archive has no direct runtime-named paths. This positive C evidence does not claim independent .olean-format attribution. Cache tooling and candidates remain private; the artifact-reading gate remains restricted to own fresh build outputs.

## Cross-validation and execution

Isla comparisons cover finite selected fixtures and sampled oracle outcomes. Their preserved mismatches and partials prevent interpreting the counts as all-input or all-choice equivalence. Observer projection equations and DIT metadata do not supply a constant-time or exact-write-set theorem.

Any executable numeric implementation has its own domain and runtime choices. Execution agreement is not promoted into a universal theorem. Exact-rational real execution and exact-only square roots retain their explicit domain limits.

## Consumer and hardware boundary

Processor identification, entry controls, address translation, memory mappings, caller contracts and run-preservation conditions remain explicit for each consumer. Model witnesses establish satisfiability in a constructed state; they do not attest an actual target. Hardware timing, speculative behavior and physical deployment admission are not established by this frozen provider package.
