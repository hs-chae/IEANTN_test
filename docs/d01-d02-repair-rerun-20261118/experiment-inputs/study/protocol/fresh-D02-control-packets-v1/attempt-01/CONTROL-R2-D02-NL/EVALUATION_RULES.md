# Submission and evaluation

Submit exact statements, full hypotheses/domains, source locators, derivations, explicit numerical obligations, reproducible scripts/certificates/proofs and remaining gaps. Report the strongest supported whole-domain portfolio for BOTH families; keep nondominated threshold/strength/premise tradeoffs and valid old minima. Distinguish original-source reuse, new derivation, conditional computation, unproved conjecture and secondary input-independent results. A result called new is not thereby globally novel or best known.

Mathematical statuses are supported at its stated trust tier, false with a concrete counterexample, incomplete with a concrete missing step, unassessed, or review interrupted. Formal Lean and source-first PV are separately reported. A written proof can be mathematically supported without full Lean; a successful numerical executable does not prove the surrounding mathematics.

Save regular flat payload files under /work/submission, preferably at most2MiB each so snapshots remain portable. Use concise filenames without directories or symlinks. Preserve large regenerable computations through deterministic scripts/parameters/hash receipts instead of huge raw dumps; explain any essential nonregenerable evidence. Include a factual completed/remaining/next-step restart note.

Write LOCK.json in EXACTLY this minimal format:
{"files":[{"path":"candidate.md","sha256":"<64 lowercase hexadecimal SHA256 of exact bytes>"}]}
List every payload exactly once. LOCK.json is the manifest and is not listed in itself. Do not add extra top-level fields. Update it after editing payloads. Save it early and at checkpoints. Harmless formatting defects can be mechanically corrected with the original snapshot retained; they do not discard assessable mathematics.

When the research stage is ready for independent review, write STAGE_STATUS.json as a regular payload and include it in LOCK.json. Use the following structure, filling each status with supported, incomplete, or no_additional_improvement and listing your actual claim files:
{"ready_for_review":true,"families":{"Ramanujan":{"status":"supported","claim_files":["candidate.md"]},"Mertens":{"status":"incomplete","claim_files":["candidate.md"]}},"serious_attempts_documented":true}
Both families need an explicit status and their actual evidence. Incomplete can be an honest completed research submission only after serious attempts and a concrete mathematical bottleneck are documented; it is not an accepted theorem. Independent mathematical review still follows. Do not copy the example statuses unless they describe your actual work.

There is no over-cap invalidation or mandatory termination at the stated planning milestones. Checkpoint, continue automatically and use the same extension policy in every treatment. Platform/provider interruption is an execution interruption, not a mathematical failure. Full mathematical review and opportunity for your own repair/re-review follow submission; that feedback contains only your own work.
