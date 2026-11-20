# IsaWitness provider status

The v9 provider uses 1,560 canonical `ArmFull` and 11 canonical `Sail` module sources at the pinned proof commit. The observer package contains 22 modules with 771 observation equations. The pinned runtime recipe reconstructs the earlier patched files and then verifies the v9 sources. [Model revision](../model/REVISION.json) · [Build and validation](BUILD.md)

The observer equation generator completed on the v9 source cut with all 771 selected forms resolved. The observer modules built against v9. The observation equation proof closures used only `Classical.choice`, `Quot.sound` and `propext`. The reviewed model header equivalence and its residual certification are available with the original comparison facts and post-pass scripts. [Equivalence report](../evidence/model-equivalence/README.md)

A clean v9 build passed all four package gates in 385.605 seconds and built the complete 1,571-module canonical inventory. The public artifacts reproduced all 12 certified header residuals. [v9 build receipt](../evidence/v9-public-cold-build.json)

The preceding source-only verification completed all four gates in 465.128 seconds and reproduced all 1,481 of that revision's artifact hashes. Its public receipt retains that measurement. [Historical source-fetch receipt](../evidence/source-fetch-cold.json)
