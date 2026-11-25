# Exact timely cube result, additive canonical integration

This is a posthoc integration of the byte-exact corrected-followup trial `cube-L2_E2_D1_V0-r1`, timely `prefix-0005/CubeTheta.lean`. The original experimental outcomes and deadlines are unchanged. `ORIGIN.json` pins the exact source; the original submitted file intentionally retains its original bytes, including its initial blank line and imports. All newly written adapters use the repository's standard headers.

`ThetaCubePopulation.v3` proves, for every **real** n >= 369, that the number of actual primes strictly between n³ and (n+1)³ is strictly greater than 0.96699 n²/log(n). The natural-number corollary starts at 369. A separate network-composition theorem consumes this new conclusion and the existing v2 conclusion to use coefficient 0.9669924 when n >= exp(8), and 0.96699 below that onset. The stronger late coefficient is retained unchanged. The coefficient comparison with the original 0.965 is proved on their common exp(6) ray.

The mathematical inputs are exactly ordinary RH, `SchoenfeldRHTheta.v1.refined_theta` (Schoenfeld1976 Theorem10, equation6.1, printedp337), and the existing `Buthe.v1.theorem_2_theta` and `theorem_2_theta_lower` (Büthe, arXiv1511.02032v2, Theorem2, equations1.6 and1.7, printedp2). These papers remain explicit literature-backed mathematical premises. The adapters prove literal correspondence to the submitted source predicates; they do not prove the source papers. `SOURCE_INPUT_MAP.json` records exact formulas, domains and canonical physical identities. The hybrid additionally takes the existing canonical v2 conclusion as an explicit premise, which the earlier complete v2 source replay already verifies under those same analytic inputs.

This is conditional **Lean kernel mathematics**, not source-first program verification. No external numerical outputs, native execution axiom, new axiom or sorry is used in the selected final theorems. The original file imports `CompactDualVerified` only for an unused `#check`; the entire import closure is nevertheless rebuilt. This import does not turn the cube proof into C/C++ source-first PV.

## Clean reproduction

Use the exact Lean compiler and generic package commits in `DEPENDENCY_PINS.json`. Obtain their ordinary compiled generic libraries with the pinned toolchain. Create a context JSON in the format shown by the existing study's `estimates/REPRODUCE.md`: exact compiler path/hash/version, eight generic package revisions, and the colon-separated paths to their `.lake/build/lib/lean` directories. The complete mathematical application is rebuilt from the checkout's sources; no previous application proof bank is required or accepted.

From the repository root run:

```sh
python3 Solutions/RH080Study.v1/estimates/early369/reproduce.py --context /absolute/context.json --run /absolute/fresh-run
python3 -O Solutions/RH080Study.v1/estimates/early369/reproduce.py --context /absolute/context.json --run /absolute/fresh-run-O
python3 -OO Solutions/RH080Study.v1/estimates/early369/reproduce.py --context /absolute/context.json --run /absolute/fresh-run-OO
python3 Solutions/RH080Study.v1/estimates/early369/test_controls.py --context /absolute/context.json --objects /absolute/fresh-run/objects --run /absolute/fresh-controls
```

`INPUT_MANIFEST.json` lists the full selected final source closure in dependency order, with module identities, checkout-relative source paths, exact SHA256 hashes and imports. The runner verifies all source identities, pinned generic package commits and compiler bytes, starts with empty application object directories, builds the full closure, and runs `EarlyAudit.lean`. The audit prints exact final types and proof-value dependencies, checks actual premise use, and restricts accepted theorem axioms to propext, Classical.choice and Quot.sound. It rejects missing providers, changed types or source hashes, unknown CLI options, duplicate/nonfinite JSON and nonfresh output paths. Acceptance uses explicit exceptions, never Python assert, and is published atomically only after successful checks and final source/controller rereads.

Controls reject substituting an unproved coefficient, onset, endpoint, missing source arguments and an unused-premise fixture. Such rejection proves an exact-contract mismatch with the existing proof, **not mathematical impossibility of the altered statement**. `VERIFICATION_SUMMARY.json` and retained receipt/log hashes record the checked runs, resources and all three Python optimization modes.

The original default `reproduce_study_all.py` and earlier frozen integration receipts cover their historical scope; they do **not** silently include this later additive v3 result. Use this new runner and the separate updated global integration receipt for v3. Generated canonical Challenge files are statement scaffolds and are never imported by the proof consumers.

## Trust and resources

Lean's kernel and generic pinned library/toolchain infrastructure, the operating system and hardware are trusted in the ordinary proof-checking sense. No claim is made about semantic adequacy of a new C/C++/CUDA program because this experiment does not introduce one. The source-only mathematical replay is host proof development, not a retroactively isolated experimental trial. The runner reserves at least 256GiB available host RAM and permits up to 32GiB address space per compiler, with actual maximum process RSS, elapsed/CPU time, final disk bytes and observed SIGKILLs reported separately. Aggregate peak RAM and peak disk are explicitly unmeasured.

There is no numerical dataset, seed, prime list or regenerable large certificate to retain: all data needed are the source files and exact dependency pins. Source receipts and concise audit logs are retained; large application build objects remain experiment-owned regenerable scratch and can be removed only after the final reproduction and evidence checks.
