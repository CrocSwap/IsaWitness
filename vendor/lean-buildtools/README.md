# Vendored gate implementation

This source subset supplies the fresh build, source scan, raw-body artifact reader and axiom-closure gate. Its exact source commit and copied file hashes are in UPSTREAM.json. The Lake configuration omits profiling and BuildMonitor targets. Provider and observer proofs must not import the metadata reader.

The artifact reader uses unsafe region access in a separate Lean process. This is an executable tool boundary, not a proof axiom allowance. The enclosing package policy rejects proof imports across that boundary. The release owner approved exactly this artifact-reader boundary. Run the gate on your own fresh builds, not on downloaded or untrusted `.olean` files, because the unsafe reader memory-maps artifact regions. BuildMonitor remains omitted.
