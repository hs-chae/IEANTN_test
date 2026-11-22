# RH continuation: mathematics, source verification and actual network reuse

This is the **post-lock continuation** of the completed ordinary-literature versus IEANTN study. The original arms, their discoveries and all earlier results are preserved. These later results are not retroactive exposure-experiment successes.

Read the standalone, offline [English research report](reports/RH_CONTINUATION_REPORT_EN.html) or [Korean research report](reports/RH_CONTINUATION_REPORT_KO.html). Mathematical expressions and fonts are embedded. The companion source/evidence tree supplies local proof links; the reports also cite original primary sources.

## Concrete results

* The same eight CH analytic source inputs plus RH now give the PNT allowance **0.181**, replacing the previously compiled **0.821**. The actual reciprocal-ordinate cap **10.5** is proved from the two existing zero-count inputs, without a new zero table.
* The new box PNT envelope strictly improves the frozen NL parabola envelope by more than **0.546** in normalized units on their common ray. Its actual C-log-to-moment-to-psi chain is source-linked and kernel compiled. The five precise analytic inputs remain explicit.
* The new reviewed octic prime-rich interval has width coefficient **2.15**, compared with the previous written **2.43**, and retains a full count/width frontier. Its conditional actual prime-count consumers, prime-index blocks and successive-cube adapter compile. The written analytic window obligations remain open in Lean.
* The same five first-Mertens source predicates plus RH give the stronger finite-band coefficient **0.014**, replacing **0.006** by retaining the cube-prime correction. The earlier-onset profile is retained separately.
* The actual all-real Ramanujan margin is **at least one twelfth from 640 billion**, with six original RH/Büthe inputs. The actual principal-value logarithmic-integral bridges and the historical truncation gap are proved. All 21 source-computed coefficients, including four initial zeros, are consumed. The larger convenient tail and full dynamic profile also compile.
* The exact GM primitive, actual weighted J identity and prime-power reindexing give a completed actual J/ordinary-pi relay with correction **14 plus the 0.2772 term**. Every one of the four published GM allowance terms is accounted for. Its pi envelopes retain the independent lower-height prime-power correction.
* Nicolas's stronger full product profile is imported as **known literature**, correcting the weak earlier 1.876 benchmark. The new Möbius power mechanism is independently reviewed written mathematics with kernel-checked components and consumers; its full complex-analysis Lean chain remains open.

The reports give the complete formulas, actual domains, exact source predicates, source locators and Pareto comparisons. The finite Büthe rows still beat the new PNT kernel on their applicable band. Published Ramanujan positivity results already have a much lower onset; the new result is a quantitative margin and improved formal/source connection, not a new positivity record. No optimality, exhaustive best-known or exposure-causality claim is made.

## Verification tiers

**PV means source-first program verification.** The two selected components bind actual C source to a restricted AST, prove its arithmetic/execution and output correctness, and consume those outputs in actual mathematical theorems:

1. `verified_finite_log.c`: all required integer-log inputs 2 through 128, proved two-sided accuracy, exact aggregation, actual box moments, actual conditional IEANTN psi bound.
2. `rh_coeff.c`: all 21 coefficient returns, actual source polynomial, actual real Ramanujan margin and profile.

The full portfolio mixes these source-first components, ordinary kernel numerical proofs, written analytic proofs and explicit published source predicates. Python rational quadrature, native prime-count scouting and directed Arb comparisons are **not** source-first PV. Native C reproduction additionally trusts the pinned ordinary compiler, runtime, OS/API and hardware contracts; the mathematical proofs use kernel-proved source-model outputs. No native execution axiom is accepted in the selected final proof roots.

The major unfinished work is explicit: the five box analytic inputs; six octic analytic/geometric contracts; the full reciprocal-zeta/Perron analytic Lean chain; the complete large finite prime-count source-first proof; and the separate 610-billion/0.076 spectral construction. A standard-three-axiom conditional theorem does not discharge its source parameters. The unused relative-Ei constant identity is not needed by the completed Ramanujan theorem.

## The actual network

Definitions-only Vocabulary provides common observables. Each versioned `Conclusions.lean` states propositions; metadata records per-conclusion input edges. Generated Challenges state conditional goals. Separate `Solutions` supply actual proofs. New analytic inputs remain unverified; locally compiled solutions are marked `lean-noncompliant` until official Comparator verification, with no fabricated receipts.

The [canonical theorem ledger](ledgers/THEOREM_LEDGER.json), [actual dependency graph](ledgers/PROPAGATION_GRAPH.json), [reuse/information recovery ledger](ledgers/REUSE_AND_INFORMATION_RECOVERY.json) and [64-family scope ledger](integration/FULL_NETWORK_SCOPE.csv) distinguish mathematical consumption from imports and from causal discovery claims. Their universe is stated explicitly; this is not a full original-source audit of every IEANTN declaration.

New versions preserve the old claims: RHSmoothing, BoxMellinInputs, RHSmoothingInputs, PrimeKernelInputs, PrimeInterval.v2, PrimeQuantile, Lcm.v4, Primorial.v2, RamanujanGap.v3, RHPrimeCounting, Nicolas, MertensRH and MobiusRH. The two open analytic input families do not have fake Solution files.

## Reproduce from a clean source tree

The pinned compiler is Lean 4.34.0-rc2. Mathlib and the other generic dependencies are pinned by commit in [GENERIC_CONTEXT.json](scripts/GENERIC_CONTEXT.json). The source, output, compiler and dependency identities are checked by the actual scripts. No prebuilt **application or LeanCert checker** objects are required. Generic library setup is separate from application proof replay.

Use Python 3.11 or later for the proof scripts, PyYAML 6.0.3 for network tooling, an ordinary C compiler for the native association runs, and the exact generic dependency/compiler pins. The independent Arb comparison was run with Python 3.12.9 and python-flint 0.9.0; it is a separate numerical tier. Report browser checks used Playwright 1.62.0. The renderer and STIX font/license are vendored under `reports/`.

Configure generic paths without changing their identities:

```sh
python3 ramanujan/configure_context.py --packages /path/to/generic-packages \
  --compiler /path/to/pinned/lean --out /scratch/generic.json
export IEANTN_GENERIC_CONTEXT=/scratch/generic.json
```

Use fresh, experiment-owned output directories. From this directory:

```sh
python3 integration/reproduce_public.py --out /scratch/rh-pnt
python3 parabolic/reproduce_clog.py --out /scratch/rh-source-log
python3 ramanujan/reproduce_strong.py --out /scratch/rh-ramanujan
python3 ramanujan/node_publication/reproduce.py \
  --strong-run /scratch/rh-ramanujan --out /scratch/rh-ramanujan-nodes
python3 signed/reproduce.py --out /scratch/rh-signed --context /scratch/generic.json
python3 signed/mobius/reproduce.py --out /scratch/rh-mobius --context /scratch/generic.json
```

The old 146-source foundation validator also pins every generic cache file, including host-specific build traces. A fresh generic build alone is therefore not byte-identical to that historical cache. The downloadable bundle's generic transport/bootstrap procedure preserves this strict original check using separate exact archival metadata and independently hash-checked generic objects; read its tested instructions before the Ramanujan command. Do not bypass or weaken the original validator. The fresh bootstrap has passed in normal, optimized and doubly optimized Python modes, including the unchanged 115,631-file historical identity gate. It downloads 8,865 exact official cache archives, builds 38 missing generic source modules, verifies all semantic/tooling hashes, and restores separately archived nonsemantic metadata in an experiment-owned regular-file view. The original validator, semantic object identities and scientific source stay unchanged. One 47,449-byte historical IDE-reference file is explicitly classified as archival tooling metadata; its kernel objects are independently exact.

From the extracted downloadable bundle root, with nine dependency source checkouts at the listed commits and the exact pinned compiler:

```sh
python3 BOOTSTRAP_GENERIC.py --packages /path/to/generic-packages \
  --compiler /path/to/pinned/lean --out /scratch/rh-generic
python3 REPRODUCE_BUNDLE.py \
  --context /scratch/rh-generic/owned-view/GENERIC_CONTEXT.json \
  --out /scratch/rh-all
```

Read `BUNDLE_README.md` for dependencies, component selection, the actual resource receipts and clean-environment setup. The bootstrap fetches generic dependencies; it does not substitute old compiled application proofs. The source-only component runs rebuild the mathematical application closures.

Run the actual optimization/mutation controls described in each track README. The integration controls include changed frozen sources, changed canonical proof sources, altered reused proof objects, missing object identities, wrong dependency/compiler pins, malformed JSON and a genuinely false Lean statement. The current reuse route requires recorded object hashes; regenerate old objectless banks instead of treating them as verified inputs.

Track entrypoints and complete recipes: [PNT integration](integration/), [C-log/kernels](parabolic/README.md), [Ramanujan and GM](ramanujan/README.md), [signed source transport](signed/README.md), [Möbius](signed/mobius/README.md). Actual receipt paths and resource use are in the reports and each `evidence/` directory.

## Evidence, resources and publication

Read [source pins](ledgers/SOURCE_PIN_SUMMARY.json) for the exact historical research base, inspected official snapshot and owner branch. The older research checkout is not silently called current upstream. Original proof artifacts and research sources remain intact.

Final accepted source replays include the complete 116-module PNT/public closure and the 46-module actual C-log closure. The latter used about 24.74 GiB peak compiler RSS; the PNT replay used about 6.68 GiB. These are measurements, not memory caps. RAM and disk were assessed separately, with a host reserve and an aggregate study ceiling. Completed runs and failed/interrupted development attempts are recorded separately; no unconfirmed SIGTERM is relabeled OOM or mathematics failure.

Only experiment-owned data proven regenerable are removed. The large native finite scout was regenerated twice with matching hashes before its temporary certificates were deleted; scripts, parameters, versions and receipts remain. Accepted proofs, sources and essential certificates are preserved. The evidence archive excludes compiled application caches and private prompts, memory or transcripts.

Publication uses the owner research branch `research/rh-full-network-20261122` in `hs-chae/IEANTN_test`. Main and unrelated branches are preserved. Exact reviewed commits, remote checks and actual downloadable artifact receipts are recorded by the parent publication handoff; no official Comparator, PR or merge is implied.
