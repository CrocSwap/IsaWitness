# IsaWitness v9 claims

IsaWitness is a frozen, Sail-derived Arm® model in Lean, built for downstream machine-code verification. The release covers four things:
- reproducible builds;
- axiom hygiene: only the three standard Lean axioms;
- equations for architectural and event-log observations;
- an accounting of how much evidence supports each part.

It makes no claim to be the first or the only faithful Arm model. It contains no proofs about programs.

## What the release contains

| Component | Contents |
|---|---|
| `ArmFull` model | 1,560 generated Lean modules, translated by Sail from the March 2023 Arm A-profile architecture sources. Source bytes match the canonical v9 proof pin. |
| `lean-sail` runtime | 11 canonical runtime modules, materialized from pinned sources and first-party additions (see [BUILD](BUILD.md)). Includes the first-party files `AbstractReal` and `AbstractRealRat`. |
| `ArmCertObservers` | 22 modules with 771 ObsGen observation equations, which project model executions onto architectural state and the event log. |
| Evidence | A 771-form instruction inventory, historical finite cross-validation against Isla, the v9 model equivalence report and build receipts. |

`ArmCert`, `ArmFull` and `ArmCertObservers` are the canonical Lean package and module identifiers. The v9 source manifest pins the corresponding model module inventory.

## Claims

1. **Reproducible model.** The 1,571 model and runtime source files match the canonical v9 SHA256 manifest. A fresh build produces a Lean artifact for each canonical module. [Recipe](REPRODUCIBILITY.md) · [Evidence](../evidence/README.md)
2. **Axiom hygiene.** For every owned declaration in the runtime, model, observer and root packages, the fresh gates report zero source errors and zero axiom errors. The only axioms permitted are `propext`, `Classical.choice` and `Quot.sound`. Each package gate checks its full owned declaration set.
3. **Observation equations.** The ObsGen equations state exactly which architectural and event-log projections they expose, and nothing more.
4. **Historical evidence accounting.** The counts retain the earlier Isla model context. The reviewed transfer boundary covers the v9 header transition. [Equivalence report](../evidence/model-equivalence/README.md)
   - The 771-form ledger records 300 forms with one category of evidence, 30 with both categories, and 441 partial forms (each with a reason).
   - Selected-case ordered traces: 737 matches, 2 mismatches, 32 partials.
   - Architectural comparisons: 706 matches, 65 partials.
   - These are different classifications. Do not add them together.

## Not claimed

- Instruction equivalence, translation correctness or hardware conformance for every input. The Isla comparisons are finite cross-validation.
- Constant-time behavior, secret independence or exact write sets. Membership in the DIT inventory is metadata, not a theorem.
- Correctness of any program, library or consumer. IsaWitness contains no proofs about programs.
- That any particular processor, firmware or operating system behaves as the model does. That requires premises and evidence specific to each deployment.

## Meaning of a theorem over this model

A theorem proved over IsaWitness establishes its stated conclusion, under its explicit hypotheses, about the frozen Sail-derived definitions. To apply it to a real machine you also need evidence that the model matches that machine, the configuration it runs in, and its callers. See [TRUST-BASE](TRUST-BASE.md).

## Scope and roadmap

Later releases will add the per-instruction step layer, the instruction-class library and generator, the value layer and the memory proof layers. They will come with a worked end-to-end example that goes from machine code to proof. Those layers are being developed separately and are outside the v9 source release. Model corrections queued for regeneration are listed in [NEXT-REVISION](../NEXT-REVISION.md).
