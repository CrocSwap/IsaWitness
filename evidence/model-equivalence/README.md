# Model equivalence and residual certification

The reviewed comparison connects the legacy-header v9 model based on commit `c0615b9e0b13bd248ecfd4fd6693a46651ae4587` to the public-header candidate at `66996aa6c2999ee014d1e222294a2601a76ffbdd`. The candidate's 1,560 `ArmFull` and 11 `Sail` source files and both deriving helper sources are byte-identical at the IsaWitness proof pin `83c8f981a6f3c6186784275044845c1ed643cbc1`. The public checkout checks these model and runtime module sources against its [canonical manifest](../../model/CANONICAL-SOURCES.sha256).

Replaying the two pinned source post-passes on the legacy v9 sources reproduced all 1,571 canonical source hashes.

The strict comparator reported nine changed public entries, three missing entries and zero added entries. All 3,371 checked private signatures matched. The residual pass examined the full model import closures, including private declarations, and classified each of the 12 differences under the approved compiler artifact rules. A fresh public build reproduced the same strict counts, private signatures and 12 certified residuals. [Cold-build receipt](../v9-public-cold-build.json)

The per-item predicates, digests and underlying data are in the [residual certification](residual-certification.json).

| Residual kind | Count | Evidence |
| --- | ---: | --- |
| Equation-lemma binder renaming | 1 | Only bound labels differ in the proposition |
| Private compiler helper visibility | 3 | Private types and kinds agree and neither closure has a cross-module consumer |
| Compile-time elaboration helpers | 4 | Full incoming-reference scan bounds them to the elaborator |
| Opaque initialization constants | 2 | Types and initialization roles agree |
| Generated match splitters | 2 | Types agree modulo bound labels and the whole parent values agree after certified private helper substitution |

Both splitter checks passed. Eight controls that changed a helper value or type, omitted a helper pair, or changed a parent value were rejected. The packaging retains the original [module conversion](packed_module_postpass.py) and [syntax exposure](expose_syntax_postpass.py) programs alongside [the controls](controls.json) and the paired [old](old.json), [new](new.json) and [splitter](splitters.json) facts. [SHA256 sums](../../docs/SHA256SUMS)

## Isla evidence

Isla ran on earlier frozen inputs. The cross-validation receipts retain those contexts and outcomes, including mismatches and partials. A fixture can transfer across the certified header transition when its model and query are bound to the legacy side and its inputs, profile, oracle choices and observation are preserved. The equivalence report certifies that header transition. A comparison from the earlier 1,481-module model still needs an evidence binding across the model revision itself. For example, the earlier `HaveEL` is a pure Boolean function, while v9 consults feature state through `SailM`. Identical observer equation text alone leaves that part of the transfer open. [Historical comparison summary](../cross-validation-summary.json) · [Earlier model source receipt](../v1-frozen-model-sources.json)
