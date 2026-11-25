# Reproduce the new estimate consumers

Use the unchanged pinned compiler/toolchain and generic source commits in DEPENDENCY_PINS.json. The small context JSON format is produced by the existing `Solutions/RHOnePrimeEvolution.v1/scripts/prepare_proof_context.py`. This helper checks the generic package versions and compiler; the new reproduction script independently checks the exact compiler bytes/version, all eight generic package names, order, Git revisions and tracked-source cleanliness. Cached generic libraries are explicit trusted dependencies; application proof objects are never reused.

Run from any working directory, substituting absolute clean paths:

```sh
python3 Solutions/RH080Study.v1/estimates/reproduce.py \
  --repository /absolute/path/to/network \
  --context /absolute/path/to/checked_generic_context.json \
  --run /absolute/fresh/path/cube_run --lane cube
python3 Solutions/RH080Study.v1/estimates/reproduce.py \
  --repository /absolute/path/to/network \
  --context /absolute/path/to/checked_generic_context.json \
  --run /absolute/fresh/path/zero_run --lane zero
```

The cube lane rebuilds15 application modules from immutable copied source, including every core declaration it needs, all three elementary transport/numerical providers, the final canonical Solution and independent exact-type/value/input/axiom audit. The zero lane rebuilds8 modules, including both actual source-bound types, center transport, final consumer and audit. No Challenge template is imported. The mathematical sources are kernel-checked with no sorry/admit/native execution leaves. Final closures use only propext, Classical.choice and Quot.sound. An ordinary official Comparator receipt is not claimed.

Each run preserves a full PLAN, exact commands, source/compiler/object/log hashes, per-command GNU time CPU/RSS, final directory usage and observedSIGKILL status. The maximum recorded per-process GNU RSS is not a sampled aggregate or exact host-wide peak; final directory size is not measured peak disk. Sequential compilation with2 Lean threads uses64GiB address-space allowance per process and a256GiB available-host-RAM admission reserve, not an obsolete4GiB cap. Exact source predicates remain mathematical inputs B.

Every run directory must be fresh. Acceptance checks remain explicit under Python normal,-O,-OO; RESULT is atomically published only after the whole source closure and final audit succeed. Failed development runs remain separately preserved.

Run exact-contract mutation controls against an accepted fresh cube object's directory:

```sh
python3 Solutions/RH080Study.v1/estimates/test_controls.py \
  --context /absolute/path/to/checked_generic_context.json \
  --objects /absolute/path/to/accepted_cube_run/objects \
  --run /absolute/fresh/path/cube_controls
```

Repeat with `python3 -O` and `python3 -OO`. The actual Lean compiler accepts the exact source contract and rejects changed unproved coefficients/onsets/endpoints, omitted finite premises, and an ignored source argument. A rejection means the old accepted proof does not establish the changed claim; it is **not** a mathematical counterexample to that changed theorem.

`build_catalog.py` regenerates the scoped source/declaration inventory directly from this pinned source and baseline Git objects. The baseline repository must retain commit25eb9bfe385be6f86c4280f92bd5f851ffe637a5. It never reads an old sorry CSV. The frozen ablation source facts are independent of the exploratory proof trajectory and must not be rewritten after trial freeze.

No random seed occurs in these deterministic proofs. Full papers and their recovered private scans are not republished; exact primary URLs, locators and SHA identities are in the source ledger and metadata. Preserve locked inputs, original primary sources, accepted proof artifacts and these scripts. Delete only previewed experiment-owned regenerable failed object/cache copies after the final source/evidence preservation gates pass.
