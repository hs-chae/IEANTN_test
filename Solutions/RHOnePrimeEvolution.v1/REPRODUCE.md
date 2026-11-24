# Reproduce the one-prime and network evolution study

The two proof packets are self-contained application-source closures. They require the pinned generic Lean/Mathlib libraries, Linux, Python 3.11, GNU time and prlimit. They do not read a predecessor application proof bank or any private numerical dataset. Each complete child pipeline was actually executed after relocation; the small combined launcher was also checked through both real child CLIs.

The mathematical statements are source-conditional. Published CMS analytic reductions remain explicit propositions, as do the inherited Green/Nicolas/BPT inputs and the historical finite-gap or finite-Goldbach hypotheses where stated. All new Gaussian integrals, actual Fourier identity, numerical objective and resulting conditional ANT consumers are kernel proved. None of this is labelled source-first C/C++/CUDA PV.

## Pins and prerequisites

- Lean `leanprover/lean4:v4.34.0-rc2`.
- Mathlib `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`; exact transitive revisions are in both packet manifests and `lake-manifest.json`.
- The first eight generic proof libraries are mathlib, plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq and batteries. Cli is additionally pinned in the generic dependency manifest but is not a selected proof library.
- The mathematical source commit is in `SOURCE_PIN.json`; the initial additive checkpoint is `f997750b9f5ba6771d226d682d8aab7e4861b315`, based on `3539bbba83db8345db1c43f37a9ddb6d8baf3ab0`.
- Both original run controllers preserve a 256 GiB available-host-RAM admission reserve and a 64 GiB per-compiler address-space cap. This is the shared study host policy, not the measured mathematical memory demand. The 300-source run with four workers sampled38.735 GiB aggregate compiler RAM; the 53-source run with two workers sampled7.862 GiB. Exact per-process GNU peaks and the sampled process-tree traces are retained. Use a host meeting the preserved admission policy; no obsolete4 GiB cap is imposed.

No generic source revision may be silently updated. Cached generic libraries are an explicit trusted dependency; the application proofs are rebuilt from the supplied source. Compiler, runtime, OS and hardware correctness remain infrastructure assumptions.

## Prepare a clean generic environment

Install elan, Git, Python and the stated GNU utilities. Clone the published `research/rh-one-prime-network-20261124` branch from `https://github.com/hs-chae/IEANTN_test`, retaining its publication files and unchanged `lake-manifest.json`. `SOURCE_PIN.json` pins the earlier scientific source checkpoint; later publication commits add the reports and delivery tooling without changing those mathematical sources. From the fresh checkout:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
```

These are generic dependency preparation commands. Do not use `lake update` to change the pins. The selected proof libraries must lie under the normal `.lake/packages/` layout; the frozen controller deliberately rejects arbitrary application search paths. The same exact dependency pins are present in the pinned Mathlib manifest. A source build of generic libraries is possible at those revisions, but was not substituted for the recorded generic-cache boundary.

Prepare explicit arguments using the actual pinned Lean executable, not an unspecified default toolchain:

```sh
python3 Solutions/RHOnePrimeEvolution.v1/scripts/prepare_proof_context.py \
  --packages .lake/packages \
  --compiler "$(elan which lean)" \
  --output /absolute/fresh/path/proof_context.json
```

This command checks every selected generic Git revision and tracked-source cleanliness, library existence and Lean version. Its output establishes dependency identity only; it is not a proof-execution receipt. The context helper and both actual packet check-only routes were exercised. In the shared original host, dependency packages were deliberately isolated for writable native hash builds; those private duplicate caches are regenerable and are not required by either delivered proof packet.

## Rebuild both complete proof packets

From the study directory or its extracted evidence copy:

```sh
python3 scripts/reproduce_packets.py \
  --context /absolute/path/proof_context.json \
  --run-root /absolute/fresh/path/reproduced-study \
  --jobs 2
```

The launcher runs these two actual front doors sequentially:

| Packet | Application sources | Verified result |
|---|---:|---|
| `portable/reproduce.py` |300|Explicit continuous/cosine one-prime frontier, finite bridge, cube/Goldbach/index consumers,24canonical targets plus helper, six mathematical mutation controls.|
| `gaussian_gap/portable/reproduce.py` |53|All Gaussian certificate providers and LeanCert foundations, genuine Fourier identity, raw numerical witness, objective, six new canonical targets,11root/12edge audit and six mathematical mutation controls.|

Both accept `--compiler`, `--generic-lean-path`, `--run`, `--jobs` and `--check-only`. Run `--help` for the exact CLI. Run directories must be fresh. Source files and controller/context identities are copied and hashed before compilation. Acceptance is published atomically only after source/object/compiler/log readback and final semantic controls succeed. Exact source types, actual proof-body dependencies, consumed numerical/source parameters and transitive axioms are checked. Allowed axioms are only `propext`, `Classical.choice`, `Quot.sound`; no native execution axiom or `sorryAx` occurs in accepted final closures.

The original successful relocated runs are in `evidence/reproduction/relocated300/` and `gaussian53/`. Their total wall times were1615.218 s and341.943 s respectively. Resource fields state exactly what was measured: aggregate RAM is sampled, individual GNU peaks are retained, and disk is final allocation rather than an exact peak. The source packet consistency hashes are not signatures or authenticity authorities; the published source commit and recorded SHA-256s identify the intended version.

## Regenerate the numerical certificate itself

`gaussian_kernel/reproduce.py` is the separate numerical-generation front door. It regenerates nine exact Lean certificate/data sources from the 13 original rational coefficients, checks byte identity, rebuilds the numerical closure and runs its exact-type/axiom audit. It needs neither SciPy nor Arb. Its actual full 32-source run and normal/`-O`/`-OO` regeneration checks passed; see `gaussian_kernel/VERIFICATION_RECEIPT.json` and its README.

The 53-source packet independently includes every selected provider needed for the final result, so it can verify the delivered source without the untrusted optimizer or generator. The generic certificate soundness theorem validates real polynomial/exponential integrals, and all564 cells, true infinite tails and pi scaling are consumed. `gaussian_fourier/README.md` documents the proved Fourier recurrence and exact25-position coefficient association. `gaussian_gap/SOURCE_LEDGER.html` renders the actual primary CMS statements and the precise analytic input boundary.

## Reproduce the external exploration and literature checks

External experiments are E and do not supply an unverified premise to the canonical theorems. Preserve coefficients, Fourier penalties, source hashes, parameters, seeds and dependency versions from the individual receipts.

- `analytic/screen_kernels.py`: deterministic multi-kernel screen; ordinary numerics.
- `analytic/search_gaussian.py`: untrusted coefficient search. The degree 12 at penalty 36/11 value near 0.834009631 is the ordinary search estimate shown in the reports. A separate matching directed-Arb output was recovered and its coefficients verified; raw execution argv and a separate OS exit receipt were not saved, so that output retains its explicit E/provenance limitations. The kernel-proved loose bound is 0.834021.
- `analytic/certify_gaussian_objective.py` and `certify_hat_witness.py`: external interval/certificate checks. The matched degree 40 value 0.833948868 and rational-hat bounds remain E. Match exact coefficients, penalty and normalization rather than degree labels.
- `comparisons/Published2026Review/reproduce_published.py`: pinned public supplement and all five original Table1 rows plus Table3. Original assertion-based upstream scripts are run with assertions enabled; they are not an optimization-safe accepted Lean provider. The campaign wrappers and their receipts are separate.
- `sources/fetch_sources.py`: exact seven primary-source byte identities. Nicely reports the below 2⁶⁴ / maximal 1550 gap claim with its stated practical qualifications; its explicitly public-domain 334,665-byte PDF is preserved because current scripted OEIS retrieval returns 403. The script records archived fallback rather than pretending it downloaded that file. All six other pinned originals were fetched and matched during the final source reproduction check.

Failed solver attempts, source/run association failures and interrupted preliminary runs are retained as failed/provisional evidence. They are not promoted to successful mathematical certificates. The legacy297-source snapshot precedes a one-comment Lee clarification; the corrected source is covered by the later complete300-source replay. Do not bypass historical current-source/path guards or rewrite their receipts.

## Reports, graph bookkeeping and evidence

The five offline HTML files use strict build-time KaTeX0.16.47, static MathML and the embedded licensed STIX font. They require no runtime JavaScript, CDN or browser extension. To regenerate from the accepted run evidence:

```sh
python3 reports/build_matrix.py
python3 reports/build_reports.py \
  --katex /absolute/path/to/node_modules/katex \
  --run /absolute/path/to/relocated300/compile
```

The renderer consumes source/receipt data separately from mathematical acceptance. Full offline phone/desktop, native keyboard, complete DOM-prose preservation and actual local-source link checks are run with `reports/check_report_browser.py`. The 30-row theorem matrix contains full quantified contracts, physical source identities, typed antecedents, endpoints and limitations.

The genuine repository commands `gen-challenges`, `check-graph`, native `ieantn_hash`, `fingerprint` and `fingerprint --check` were executed, covering 380 ordinary core modules after the new nodes. Generated Challenge templates deliberately retain the repository's proof placeholders; accepted Solution proofs do not import them. Official Comparator approval remains absent: its actual entry point stopped at missing cargo. No local report or verifier is presented as that approval, and metadata retains local-review status.

`evidence/reproduction/COMPILER_AUDIT_LOGS.zip` contains 1814 byte-identified copied compiler/control logs plus their original manifest. Nineteen JSON/CSV/source-delta files remain readable alongside it. The deterministic archive, every member and the retained files were checked in normal/`-O`/`-OO`, including metadata/payload mutation controls. `evidence/log_archive.py` and `test_log_archive.py` reproduce those checks. All original accepted run artifacts remain preserved independently.

## Storage cleanup

Only previewed experiment-owned duplicate caches, verified copied logs and regenerable failed/intermediate objects may be removed after their reproduction routes pass. Never remove the original sources, locked inputs, accepted proof artifacts, essential coefficient data, source/proof receipts or the only regeneration copy. The final cleanup receipt states exact targets and retained replacements. Historical outcomes and the default Git branch are preserved; new proof work is additive research.

## Verify and reconstruct the downloadable evidence bundle

The ZIP is a portable research export, not a replacement for the whole inherited Git repository. Its `BUNDLE_MANIFEST.json` lists every included file, byte count and SHA-256. The two self-contained proof packets can be run from the extracted export with the checked generic environment above. The complete canonical network is available from the published branch.

```sh
python3 Solutions/RHOnePrimeEvolution.v1/scripts/build_evidence_bundle.py verify \
  --archive /absolute/path/RH_ONE_PRIME_SOURCE_AND_EVIDENCE.zip \
  --extract /absolute/fresh/path/extracted-study
```

After extraction, deterministic re-creation uses the same script with `build --repository /absolute/path/extracted-study --selection /absolute/path/extracted-study/BUNDLE_MANIFEST.json --output /absolute/fresh/path/recreated.zip`. The archive builder checks every selected source byte before writing and verifies the complete archive afterward. Acceptance uses explicit checks in normal Python, `-O` and `-OO`. SHA-256 values for the deliverable files are also supplied separately.

Final cleanup removed only 9.151 GB of apparent owned duplicate generic caches and interrupted-v1 objects (9.643 GB allocated); all accepted proof banks and original pinned providers remain. `evidence/cleanup/` records the exact preview, original provider pins and result. The current development checkout intentionally has no generic-package symlinks after cleanup: hydrate private package copies before any future native core build. This does not affect either portable proof packet.
