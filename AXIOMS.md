# Axiom policy

Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
No additional proof axiom exceptions. New exceptions require explicit release-owner approval, an exact name, approval date, reason and removal plan. Do not use native evaluation to prove
theorems. `archive/` is historical, excluded from Lake roots, and never imported.


## Metadata tool boundary

Release-owner approval dated 2026-11-10 covers only the artifact reader below. These executable tool implementations are never proof premises. No proof axiom allowance changes. The gate rejects proof imports across the tool boundary. The gate enforces this boundary. Run it on your own fresh builds, not on downloaded or untrusted .olean files: the reader memory-maps artifact regions via unsafe reads.

```json
{
  "tool_roots": [
    "vendor/lean-buildtools/lean_buildtools/lean"
  ],
  "exceptions": [
    {
      "name": "BuildTools.AxiomGraph.expressionIdentity",
      "scope": "tool",
      "locations": [
        "vendor/lean-buildtools/lean_buildtools/lean/AxiomGraph.lean"
      ],
      "date": "2026-11-10",
      "approved_by": "release owner",
      "reason": "Executable metadata reader outside every proof closure; this name denotes an unsafe implementation, not a proof axiom.",
      "removal_plan": "Remove the vendored reader if the gate becomes a separately available public dependency."
    },
    {
      "name": "BuildTools.AxiomGraph.dumpModule",
      "scope": "tool",
      "locations": [
        "vendor/lean-buildtools/lean_buildtools/lean/AxiomGraph.lean"
      ],
      "date": "2026-11-10",
      "approved_by": "release owner",
      "reason": "Executable metadata reader outside every proof closure; this name denotes an unsafe implementation, not a proof axiom.",
      "removal_plan": "Remove the vendored reader if the gate becomes a separately available public dependency."
    },
    {
      "name": "BuildTools.AxiomGraph.run",
      "scope": "tool",
      "locations": [
        "vendor/lean-buildtools/lean_buildtools/lean/AxiomGraph.lean"
      ],
      "date": "2026-11-10",
      "approved_by": "release owner",
      "reason": "Executable metadata reader outside every proof closure; this name denotes an unsafe implementation, not a proof axiom.",
      "removal_plan": "Remove the vendored reader if the gate becomes a separately available public dependency."
    }
  ]
}
```
