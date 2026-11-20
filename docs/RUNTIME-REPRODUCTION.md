# Reproducing the runtime sources

`scripts/fetch-lean-sail` obtains Git revision `c816ea7ad03cce98d51acee252540fd4215fede8` and checks its tree and each input SHA256. The tracked [runtime manifest](../vendor/lean-sail/UPSTREAM.json) pins the input files, edit recipe, intermediate legacy output and final runtime/configuration bytes.

The edit recipe records affected paths, zero-based upstream line ranges and SHA256 values for the old slices. Replacement fragments contain new text and checked references to existing byte ranges. The first two stages recreate the previous patched payload byte for byte. A third stage brings the upstream-derived modules to the canonical v9 source pin. The two first-party `AbstractReal` sources ship directly. Of the 520 nonblank additions in the previous patches, 20 matched a nonblank upstream line after trimming whitespace. The edit recipe represents all 20 by source references. [Edit audit](../evidence/runtime-edit-audit.json)

The fetcher validates the complete output before installation. Later runs verify the existing output. `python3 tools/check-model-reproduction.py` checks that the 11 runtime modules agree with the canonical proof sources. The fresh runtime gate checks the default build and the raw declaration bodies, including the runtime test modules. [Validation recipe](BUILD.md)

Earlier runtime artifacts used multiple incremental compilation profiles. A controlled reconstruction attributed the retained byte differences to source paths, synchronous elaboration and a build-monitor plugin that affected generated binder names. The public build uses uniform standard options. [Historical diagnostic](../evidence/runtime-monitor-diagnostic.json)
