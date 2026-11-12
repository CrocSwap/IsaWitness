# IsaWitness v1: what is claimed

IsaWitness is a frozen, Sail-derived Arm® model in Lean, built for downstream machine-code verification. The release covers four things:
- reproducible builds;
- axiom hygiene: only the three standard Lean axioms;
- equations for architectural and event-log observations;
- an accounting of how much evidence supports each part.

It makes no claim to be the first or the only faithful Arm model. It contains no proofs about programs.

## What the release contains

| Component | Contents |
|---|---|
| `ArmFull` model | 1,481 generated Lean modules, translated by Sail from the March 2023 Arm A-profile architecture sources. The source bytes are frozen. |
| `lean-sail` runtime | Pinned upstream runtime sources, fetched and checked against hashes (see [BUILD](BUILD.md)). Includes two first-party files: `AbstractReal` and `AbstractRealRat`. |
| `ArmCertObservers` | Six modules of ObsGen observation equations, which project model executions onto architectural state and the event log. |
| Evidence | A 771-form instruction inventory, finite cross-validation against Isla, build receipts and gate receipts. |

`ArmCert`, `ArmFull` and `ArmCertObservers` are the canonical Lean package and module identifiers. They stay unchanged so builds remain byte-reproducible.

## Claims

1. **Reproducible model.** A fresh build from the pinned sources reproduces the canonical SHA256 of every one of the 1,481 model artifacts. The recipe is in [REPRODUCIBILITY](REPRODUCIBILITY.md); the receipts are under [evidence](../evidence/README.md).
2. **Axiom hygiene.** For every owned declaration in the runtime, model, observer and root packages, the fresh gates report zero source errors and zero axiom errors. The only axioms permitted are `propext`, `Classical.choice` and `Quot.sound`. The audit covers 1,394 runtime declarations, 46,177 model declarations and 4,158 observer declarations.
3. **Observation equations.** The ObsGen equations state exactly which architectural and event-log projections they expose, and nothing more.
4. **Evidence accounting.**
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

Later releases will add the per-instruction step layer, the instruction-class library and generator, the value layer and the memory proof layers. They will come with a worked end-to-end example that goes from machine code to proof. Those layers are being developed separately and are not part of v1. Model corrections queued for regeneration are listed in [NEXT-REVISION](../NEXT-REVISION.md).
