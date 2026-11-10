# IsaWitness: current scope and claims

> Documentation preparation draft.

## What this package contains

IsaWitness is the public repository name; ArmCert, ArmFull and ArmCertObservers remain canonical Lean package/module identifiers. This package checkpoint contains 1481 frozen ArmFull model modules, 15 Sail runtime/test sources, 6 observer modules, a 771-form instruction inventory, retained comparison evidence and import/test entry points. The model sources preserve the frozen bytes. Runtime and observer copies record limited opening-comment normalization separately from their declarations.

The included ObsGen equations expose event-log and architectural observation projections of the model execution. They describe those projections; they do not prove instruction equivalence, exact write sets, secret independence or hardware timing. DIT inventory membership also does not prove secret independence.

The per-form step proof library, changing value layer, instruction-class library, pipeline generator, physical-memory proof layer and walk/translation cleanup packages remain outside this checkpoint. Program and library release claims are outside it. See the [instruction inventory](../evidence/instruction-inventory.json) and [evidence scope](../evidence/README.md).

The current source-only runtime layout distributes UPSTREAM.json, an ordered patch series, and the two first-party AbstractReal/AbstractRealRat sources. A POSIX shell/Git fetch obtains 13 runtime/test sources, retaining 2 first-party sources, and verifies 23 raw-file SHA256 pins across sources, configuration, patches and series. The applicable local Lean package is still lean-sail. Source identity checks reject edited, partial or extra source payloads; package-owned .lake build metadata is outside that inventory.

## Meaning of a formal result

A theorem over this model establishes its exact stated conclusion under its explicit hypotheses. It does not by itself establish the intended deployment, a physical processor profile, operating-system behavior, an arbitrary caller or a hardware timing guarantee. Those require separately bound premises, proofs and deployment evidence.

The frozen source includes recorded model/runtime choices and corrections. Cross-validation with Isla supplies finite comparison evidence; it is not a proof of correctness of Sail-to-Lean translation or of every possible oracle outcome.

## Inventory and finite comparison evidence

The historical 771-form ledger retains 300 forms with one evidence category, 30 with both, and 441 partial with recorded reasons. The later selected-case ordered comparison has 737 matches, 2 mismatches and 32 partials; the architectural comparison has 706 matches and 65 partials. These are different classifications of finite evidence and must not be added together.

The [selected-case index](../evidence/selected-cases.json) and [report manifest](../evidence/selected-cases-manifest.json) retain 1525 public report projections with source/projection hashes, premises, incomplete cases and proof-credit flags. The ordinary CSDB/SSBB trace mismatches remain visible. An observer-only diagnostic does not repair them. This package retains historical receipts, rather than claiming a fresh empirical rerun or a portable standalone replay bundle.

## Completed build checkpoint

The earlier source checkpoint’s [complete cold-build receipt](../evidence/complete-cold-build.json) records fresh default-target builds and owned-declaration raw-body gates for lean-sail, ArmFull, ArmCertObservers and ArmCert, using Lean 4.35.0. All four passed with zero source or axiom errors. The audits cover 1394 runtime, 46177 model and 4158 observer declarations; the two import/test roots own no declarations. The complete run took 431.711 seconds without restoring compiled artifacts.

All 1481 model artifacts reproduced the canonical SHA256 identities. Runtime acceptance uses its documented uniform recipe and fresh gate; this does not claim reproduction of every historical runtime artifact. This completed build checkpoint does not approve publication. The public repository name is IsaWitness, and first-party code, including the vendored first-party lean-buildtools implementation, uses Apache-2.0. Copyright (c) 2026 Crocodile Labs Inc. The exact AxiomGraph metadata-reader tool boundary is release-owner ratified; it adds no proof axioms and remains outside every proof closure. Third-party runtime permissions, final committed source/cache acceptance and review of the final branding, licensing and warning changes remain pending. The first-party license does not relicense third-party material or establish permission to distribute unresolved upstream sources.

The build receipt identifies source archive SHA256 c9ae555045cc4c932a216b72f1ce0fb5490c0eddd2348fef541a778bac5327fa and source manifest SHA256 6f96eae059bc07b139b40bcb8fab266f19174800f033120fd75fd0cb9925ca0c. These identify the measured source checkpoint while final release metadata is pending; they do not promise a public download or published release.

A clean source-only fetch followed by the four fresh package gates reproduced all 1481 canonical model artifact hashes in 465.128 seconds, about 7.8 minutes on the measured machine. The measured run fetched immediately before the original cold helper. Subsequent fetch guards, build-metadata handling and internal fetch wiring were checked separately; all source/configuration/payload pins remained identical to the built inputs. This is source/configuration-equivalent cold evidence, not an exact-final-wrapper cold run or a general time guarantee.
