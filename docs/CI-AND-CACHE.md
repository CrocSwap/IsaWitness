# CI and prebuilt artifact preparation

The source workflow materializes the pinned runtime and checks all canonical model and runtime source hashes on a hosted runner. The manual cold build runs on the main branch using an isolated Linux AArch64 runner labelled `isawitness-release`. Provision the pinned Lean toolchain, Python 3.11 or later, and the `release-build` environment with the required owner approval.

The heavy workflow runs `tools/run-cold-build.sh` with a 600-second job limit. Each package enforces its source and raw-body check budget. Start with a fresh checkout for a cold measurement. The wrapper disables artifact restoration and can be run locally.

```sh
bash tools/run-cold-build.sh
```

Results default to `.lake/validation/`, outside source scanning. CI checks use a full commit pin for the official checkout action with persisted credentials disabled. GitHub's [self-hosted runner documentation](https://docs.github.com/en/actions/how-tos/manage-runners/self-hosted-runners) and [secure use reference](https://docs.github.com/en/actions/reference/security/secure-use) describe runner and workflow configuration. The heavy workflow does not process pull requests on the release runner.

The current release plan is source-only: fetch the pinned runtime and build locally. Runtime, model and native prebuilt caches remain private until upstream runtime permission is resolved. Model-generated C contains runtime specialization function bodies, so excluding only the separate runtime archive does not establish a runtime-free model cache. The following native Lake cache work is private preparation for a later permission decision. Lean 4.35's [Lake documentation](https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/README.md#github-release-builds) documents package release archives. `lake pack` packages an existing package build; it does not build or certify it. Package archives are platform/toolchain-specific distribution inputs and need accompanying source, license and acceptance identities.

A matched set of four native Lake package archives passed a separate-checkout round trip. Every compiled artifact and native dependency/output hash was preserved; only trace diagnostics, setup metadata and archive ownership were normalized. Lake accepted the complete default build with `--no-cache --no-build`, all 1,481 artifact hashes for the preceding model matched, and a changed model source correctly caused a stale-cache rejection. See [cache-roundtrip.json](../evidence/cache-roundtrip.json). These archives derive from our own fresh four-package build; consuming them does not constitute a fresh gate. The raw archives remain private because they contain build-path metadata. Frozen model assertion strings remain covered by the documented diagnostic-string exception.

The v9 release plan uses a source-only checkout. Source export review and explicit owner approval precede publication.
