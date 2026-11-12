# IsaWitness v1: limitations

## Scope
- The 771-form inventory and the observation equations do not certify any instruction end to end.
- Per-form step proofs are deferred.
- The value, instruction-class, generator, physical-memory and walk layers are not included.
- Proofs about programs and libraries are not included.

## The frozen model's source and choices
- **Source vintage.** The model is translated from the March 2023 Arm A-profile architecture sources. It keeps the behavior of that release, including issues that Arm fixed later.
- **Known issue: stage-2 overlay flag.** In classic stage-2 direct permissions, an inactive overlay flag can be left unspecified. Arm's 2026-06 and 2026-09 sources initialize it to false.
  - A consumer that relies on inactive-overlay behavior on that path must state, as a premise, that the flag is false at every reached invocation.
  - The regeneration check is tracked in [NEXT-REVISION](../NEXT-REVISION.md).
- **Runtime choices.** Recorded runtime choices and source corrections are part of the frozen semantic target.
- **Real arithmetic.** Real arithmetic executes over exact rationals, and square roots are supported only when exact. Both have explicit domain limits.
- **Excluded instructions.** Runtime optimizations do not certify excluded FSQRT instructions.

## Finite evidence
- The ledger keeps 441 partial forms.
- Selected ordered traces keep 2 mismatches, both ordinary CSDB/SSBB trace differences, and 32 partials.
- Architectural comparisons keep 65 partials.
- These are historical, finite report projections. They are not all-input or all-oracle-choice equivalence.

## Frozen diagnostic strings
The generated model keeps 2,244 build-path string literals across 306 modules. They are inert assertion-message data:
- a comment-aware scan found no file read, include, initialization or evaluation hook that uses them;
- builds do not need the original directories to exist.

Normalizing them would change model bytes, so it is deferred to the next model revision.

## Distribution
- Upstream runtime permissions are still unresolved ([lean-sail#24](https://github.com/rems-project/lean-sail/issues/24)).
- The release is therefore source-only: the runtime is fetched from upstream at a pinned commit and checked against hashes, and you build locally.
- No prebuilt runtime, model or native cache is distributed. Model-generated code contains runtime specialization bodies, so a model cache would not be free of runtime code.
- Software Heritage archival of the pinned runtime commit is unconfirmed.
