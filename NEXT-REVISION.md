# Next model revision

Changes here require a planned model revision with source review, regeneration, fresh builds/gates and consumer migration. Existing freeze receipts do not certify modified source bytes.

The frozen model retains a limitation from the March 2023 source in classic stage-2 direct permissions: an inactive overlay flag can remain unspecified. The [official 2026-09 ASL archive](https://developer.arm.com/-/cdn-downloads/permalink/Exploration-Tools-A64-ISA/ISA_A64/ISA_A64_xml_A_profile-2026-09.tar.gz) contains 2026-06 and 2026-09 sources whose direct helper explicitly initializes that flag to false. Those later repairs are outside this freeze. For the affected classic direct path with overlays disabled or unsupported, consumers relying on inactive-overlay behavior must expose the temporary premise that this unspecified Boolean is false at every reached invocation. This is an additional model premise, not a theorem about all model choices.

- Re-check classic stage-2 inactive-overlay initialization against the newer official source during regeneration, review the exact repair, then migrate consumers and retire the temporary restricted-domain premise where applicable.
- Reconcile retained model/runtime defect and scope limitations before expanding instruction or physical-profile coverage. Keep moving value, class, generator and physical-memory layers outside this frozen provider until separately accepted.
