# Additive preparation for a clean-root exposure rerun

This directory preserves eleven exact generic runtime source/config components needed by the existing native executor, including the actual dynamic `research_session.py` → `native_session_core.py` import. It contains no account credentials, private account configuration, worker prompts, model outputs, session state, system context or trajectories. Sources/configs are the project-owned reviewed runtime under the repository license; exact identities are in `SOURCE_COMPONENTS.json`. Existing frozen trial adapters, protocols, source pins and outcomes are unchanged.

The original public backend already exists under `Solutions/RHExposureStudy.v1/study-backends/layout/`. Its SHA is `89784de8153c616219a4a93d23f1859845d18924ad472d0d6321fb0eb2661091`. The old RH080 adapter still uses its historical absolute workspace path; the additional generic files here fill the actual source/config dependencies rather than pretending the complete runtime was already in that older public layout. The source-identity JSON records historical paths as provenance. It is not an account-state file or a new runtime acceptance.

Run a source/available-tool/corpus inventory without starting a worker, calling a model or reading account credentials:

```sh
python3 -OO Solutions/RH080Study.v1/exposure-runtime/inspect_replay.py \
  --repository /absolute/network \
  --corpus /absolute/fresh/reconstructed-corpus \
  --output /absolute/fresh/runtime-inspection.json
```

Omit `--corpus` to list exact missing inputs. A passing source audit explicitly says **not ready for research trials**. The script checks every source hash and parses all Python sources; it records installed tools/versions and checks any supplied corpus against all66 frozen file hashes. This is metadata/source preparation, not an actual isolation fixture or a mathematical proof.

`CORPUS_RECIPE.json` gives primary URLs and exact PDF/supplement hashes, all frozen corpus files, baseline commit25eb9bfe, and PyMuPDF1.27.2.3 extraction settings. Fetch actual PDF/supplement bytes through their public source records; a DOI landing page is not the required file. Require exact hashes before extraction. Recreate supplement paths and text exactly. The five main paper identities, corpus additions and assigned equality of numerical information remain unchanged. A source served differently today is not permission to replace a frozen input.

Some frozen artifacts, including recovered source scans, the exact extracted text and derived baseline reports, may have no direct byte-identical public locator. Their provenance/hash and matching research-commit source remain recorded; a missing copy is a real reconstruction blocker. The current original corpus has been retained by the study, but is not silently republished here as if all papers and derived packet content were included in this small source preparation folder.

For a freshly prepared, separately reviewed packet/runtime/lock under an explicit clean data root, the additive adapter can invoke the **unchanged** original metadata gate:

```sh
python3 -OO Solutions/RH080Study.v1/exposure-runtime/check_lock.py \
  --repository /absolute/network \
  --data-root /absolute/fresh/exposure-data \
  --lock /absolute/fresh/exposure-data/trial/EXECUTION_LOCK.json
```

Use `--fixture` only for an actual fixture lock. This adapter rebinds the data/backend locations explicitly, then always invokes the original `--check-only` route. It preserves the original protocol/pin/mount/fixture/premise/fresh-output checks. It does not rewrite lock paths, invent a reviewed fixture receipt, produce execution approval, or launch a model. Use the separately tested full fixture launcher below for actual namespace execution. A new root requires newly reviewed locks; historical locks remain evidence, not portable launch authority.

A full new exposure run additionally requires these external/reconstructed components:

1. The exact source-assigned packet, corpus representation, generic Lean/package trees and, for V1, the exact admitted C source/proof cone. Use `pv/V1_PROOF_CONE_MANIFEST.json` as the evidence identity and reconstruct from the new deterministic proof run; never mount unrelated G80/G56/new-cube answers. Preserve matched conditions and the original4CPU/64GiB/12GiB-scratch trial budgets.
2. The exact mpmath and sympy source trees recorded by the preserved `runner_python_package_trees.json`; version strings alone do not reproduce their per-file source identities. Recreate these under the new backend's `coordinator/runner-generic-python` and check the full trees.
3. A compatible Linux namespace executor and actual bounded cgroup CPU/RAM/scratch applicability. The exact intended mounts must pass a newly executed no-model fixture and the original successful-fixture gates. Do not bypass those checks or widen access if reconstruction fails. The default4GiB in the old base adapter is overridden by the assigned-runtime layer, which applies the locked64GiB trial limit; coordinator proof replay has separate larger allowances.
4. The pinned native Codex executable/runtime and a configured native account. These are external infrastructure. Credentials stay with the trusted controller and are neither copied here nor mounted into research workers. Generic shell/config/hook source is preserved; executable/service availability is not established by those source files.
5. A new reviewed root/packet/runtime/source/run association. Existing `prepare_packets.py`, `prepare_runtime_locks.py`, `prepare_v1.py` and `run_screening.py` record the actual old procedure, but their hardcoded historical root must be handled by an additive reviewed rerun adaptation rather than editing the frozen originals. Use the parameterized reference preparer and execution transport described below. A new research task requires a successful fixture for that identical task packet and its intended mounts.

No additional model trial was run. The fixed exposed model alias had no immutable service revision or replay sampling seed, so future model outputs cannot be promised byte-identical. New procedural reruns must record their live catalog/runtime and remain separate experiments. Deterministic numerical/Lean reproduction is provided by `../reproduce_study.py` and does not need this native backend, any account, or the original large exposure object bank.

## Actual clean-root execution and public reference templates

The additive fixture launcher has passed the complete clean-root NOAUTH run through the unchanged original `run_screening.accept_fixture` routine, including consistent exported artifacts, absent account/host/controller canaries, and distinct PID/network namespaces. Actual native client and executor were both Codex0.172.0. This is a deterministic local fake-provider fixture, with zero real model inference; its records remain supplemental reproduction evidence.

Both actual follow-up proof-support variants also passed inside their intended namespaces. `CompactDualVerified` imported through actual `/bin/lean` in V0 and V1, and the selected theorem axiom closures were exactly the standard three. `CompactDualSourceFirst` and its joint source-first theorem imported only in V1; V0 had neither its object file nor an available import. The actual wrapper exported `/source_pv/objects` and the assigned generic libraries and called `/opt/lean/bin/lean -j4`. Plain copied `.olean` files sufficed for these selected real imports and axiom audits; no private/server companion artifact was missing. Exact proof source, stdout and receipts are in `PROOF_IMPORT_MANIPULATION.json` and `../reproduction-evidence/`.

`references/` preserves portable primary/followup-V0/followup-V1 templates and all exact per-file source/content tree inventories. These templates contain hashes, not paper or account contents. They replace dependence on an original private lock pathname. Supply explicit source roots to construct a new reference:

```sh
python3 -OO Solutions/RH080Study.v1/exposure-runtime/prepare_reference.py \
  --repository /absolute/network --template followup-V0 \
  --root /absolute/fresh/reference \
  --toolchain /absolute/pinned/lean-toolchain \
  --packages /absolute/network/.lake/packages \
  --generic-source-root /absolute/filtered-pinned-generic-source \
  --corpus /absolute/reconstructed-frozen-corpus \
  --representation /absolute/reconstructed-E2-representation \
  --support /absolute/reconstructed-D37-support

python3 -OO Solutions/RH080Study.v1/exposure-runtime/launch_fixture.py \
  --repository /absolute/network --root /absolute/fresh/noauth-fixture \
  --reference-lock /absolute/fresh/reference/REFERENCE_FIXTURE_LOCK.json \
  --python-packages-root /absolute/pinned-mpmath-sympy-source \
  --codex-client /absolute/native-client/bin/codex \
  --codex-executor /absolute/native-executor/bin/codex \
  --proof-mode V0
```

Use `followup-V1` and `--proof-mode V1` for the additional C49 support. `primary` is the original E1/V0 environment and does not require `--support` or a proof-import probe. The preparation step alone is not acceptance. The launcher hashes every actual supplied tree against the frozen inventory, preserves the declared trial resources and exact runtime source bytes, recreates pinned mpmath/sympy sources in its fresh owned root, and uses only the local fake provider with an empty account profile. `--mount-map` explicitly remaps targets if needed; remapped content must still match every frozen file. The exact full-tree checks are never skipped.

The actual public-template test used fresh controller/packet/manifest/Python roots and explicit pre-existing pinned generic/corpus/representation/support inputs. It did not claim to have downloaded all sources again from the Internet. Exact corpus reconstruction, including recovered scans without a byte-identical public locator, remains a disclosed external input requirement. Rebuilt generic/application objects must match the selected frozen identities before being described as that exact treatment.

`run_reviewed.py` is the separate clean-root fixture/research transport. It defaults to the unchanged metadata-only gate. With `--execute-reviewed`, explicit runtime paths, and a valid freshly reviewed lock, it invokes the original executor without editing its source. Fixture execution is independently accepted by the original fixture routine. Research execution additionally retains the original successful-fixture, matching packet/runtime, model, budget and bounded-cgroup checks; it requires a configured native account. No research execution was requested by this reproduction work. An actual research lock must reference a successful fixture for its **own identical task packet**; the neutral proof-import canary does not authorize a different research packet.

```sh
python3 -OO Solutions/RH080Study.v1/exposure-runtime/run_reviewed.py \
  --repository /absolute/network \
  --data-root /absolute/fresh/exposure-data \
  --lock /absolute/fresh/exposure-data/trial/EXECUTION_LOCK.json
```

The command above only checks metadata. For a separately authorized execution, add `--execute-reviewed`, explicit `--python-packages-root`, `--codex-client`, `--codex-executor`, and `--fixture` only when the supplied lock is a fixture lock. Run research execution inside the original locked bounded cgroup; the adapter does not create host privileges or bypass `check_scope`. A valid source package and account are ordinary external dependencies, not evidence of a successful run.

The generic source views themselves are reproducible from the pinned public Git repositories:

```sh
python3 -OO Solutions/RH080Study.v1/exposure-runtime/prepare_generic_sources.py \
  --repository /absolute/network \
  --packages /absolute/network/.lake/packages \
  --out /absolute/fresh/filtered-pinned-generic-source
```

This command uses `git archive` at each exact pinned commit, excluding Git metadata, caches and untracked workspace files, then requires the complete generated tree to match its frozen manifest. The actual nine-package reconstruction (eight generic libraries plus Cli source) passed; temporary tar archives were deleted after hashing. It does not compile or copy an old application object bank.
