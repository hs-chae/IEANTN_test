# Spectral transfer and actual Ramanujan620 continuation

This directory belongs to the new RHLimit study. Historical RHContinuation and exposure outcomes are unchanged. Read the JSON receipts before treating a branch as accepted.

## Mathematical results

* `SpectralGMRefined.lean`: from the exact four-term Grenié–Molteni rational-field primitive inequality, RH, and the existing two Büthe anchors, proves the actual compensated J error at every real x≥exp12 is at most14.44+.1386sqrt(x)/(log(x)(log(x)−6)). The old14+.2772sqrt(x)/log²(x) bound exceeds the new one by more than.2 on the entire ray x≥exp16. This source is frozen for the root’s actual ordinary-π consumers.
* `NicolasSpectralMass.lean` and `BetaDecimal.lean`: the existing canonical Nicolas source119 implies actual inverse-square zero-mass summability and mass<.047. The source is used only at legal x>1; a uniformly convergent phase-series right limit recovers the mass at1. This does not by itself prove the .076 transfer: exact integrated-explicit-formula/oscillatory interchange calculus is still required.
* `Ram620Low/Anchors/Powers/Bands/Finite/Leaves/Result.lean`: derive actual finite prime-power bounds and transfer two published Table1 rows through the new GM profile. The final proved consumer adds normalized actual Ramanujan gap≥.001 on620b≤x≤640b and retains the basic predecessor1/12 and4/5 margins above640b. `RAM620_RESULTS.json` records the complete accepted source replay and actual final consumers.

The620b milestone does not close the earlier610b/.001 construction. The proof compares under the explicit union of existing source inputs. In particular, the new finite branch uses Table1 and the exactGM source, while the old≥640b branch retains Table2. The canonicalv3 network also retains stronger p20max and large-log profiles; preserving those requires the separate rootv4 glue. This component does not claim preservation of that entire stronger canonical profile, a globally larger scalar margin or a best-known result.

## Exact source contracts

* Grenié–Molteni, arXiv1312.4465v4, Theorem1.1 rational-field display, PDFp3: under RH, x≥3, the modulus of the actual first ψ primitive minus x²/2 is ≤.0462x^(3/2)+1.838x+1.9851+.5097/x. All four terms are retained.
* Büthe, arXiv1511.02032v2, Theorem2 Eq1.5,1.8,1.9,1.10, PDFp2; Table1 PDFp14; Table2 PDFp16. Table1 at16×10^10 is(−.88,.68), at32×10^10 is(−.88,.78), on each closed dyadic interval. Note Eq6.2 is a separate small-height interval in the paper; the620 bridge invokes Table1 itself.
* Nicolas, arXiv1202.0729v2, Eq1.18–1.19 printedp4, with β inEq1.3: actual spectral W under RH, all x>1.
* The imported≥640b tail retains the existing explicit Büthe2016 input, its source domains, and the already proved actual principal-value li bridge.

No standalone Blueprint label exists for these newly created refinement lemmas. Their imported correspondences are `IEANTN/Nodes/Buthe/v1/Conclusions.lean` and `IEANTN/Nodes/RHPrimeCounting/v1/Conclusions.lean`, plus the unchanged exact source predicates in `Solutions/RHContinuation.v1/ramanujan/ActualGMTransfer.lean` and `signed/source/NicolasBaseline.lean`.

## Verification and trust

The new analytic and scalar proofs are Lean-kernel proofs. They are **not source-first PV**. The actual degree20 polynomial consumer reuses the existing source-first C coefficient component. Neither Python scouting nor `interval_decide` is relabelled PV. Final axiom printouts must contain only propext, Classical.choice, Quot.sound; no newaxioms, sorry, native_decide or native execution facts are accepted. RH and precise published analytic statements remain explicit theorem arguments, not hidden Lean axioms.

`compile_development.py` snapshots the selected proof source, pins the compiler, hashes its read-only application-bank objects, compiles with8threads under80GiB address space, captures `/usr/bin/time -v`, and checks printed theorem dependencies. Its default historical banks support development, not a fresh whole-source replay. Supplying `--foundation-library` replaces those defaults; the complete fresh source replay is now accepted in `evidence/cold55-v1/RESULT.json`, with exact resource and source association.

## Complete source-only reproduction

The decisive replay uses the root’s cold261 source basis, followed by the exact55 additional imported/new modules in `SOURCE_CLOSURE.json`. All55 are frozen here, including the unchanged rh_coeff.c source. The root’s PNTFullRH module identity is retained; every old Ramanujan consumer is freshly compiled against that coherent identity. The55 include nine new modules and46 pre-existing application dependencies; they are not55 newly invented numerical programs.

From the network root, with the pinned generic context configured:

```sh
python3 Solutions/RHLimit.v1/scripts/reproduce_pi_complete.py --out /data/cold-pi261
python3 Solutions/RHLimit.v1/spectral/reproduce_cold_append.py \
  --basis /data/cold-pi261 --out /data/cold-spectral55
python3 Solutions/RHLimit.v1/spectral/controls_cold_append.py \
  --basis /data/cold-pi261 --out /data/spectral-controls
```

The append controller refuses an unfinished or changed basis. It checks every basis source, object and log hash, exact compiler/generic revisions, all55 frozen source imports and C resources, final theorem axioms and actual compiler dependency paths. It uses no historical application or LeanCert object cache. This gate passed for the study: a fresh261-source basis, an explicit fresh23-source resource correction, and all55 additional sources. The initial V1 recipe was two-stage; it is preserved as such, and the clean default uses the resource-complete controller. See `evidence/cold55-v1/RESULT.json` and `RESOURCE_ACCOUNTING.json`. The prior ten-module repeat against historical accepted banks was interrupted with exit143 and is not accepted as a complete replay; the original individual kernel passes and independent seven-source reviewer passes remain valid.

## Incremental development reproduction

Use the pinned Lean4.34.0-rc2 compiler, Mathlib commit71a80585ee495fc24472fd0eaffc89d94e4fd8d6, and the exact sources/dependencies recorded by the complete RHLimit study controller. That controller must first rebuild the imported mathematical application sources and LeanCert kernel layer. The runner here intentionally does not treat a precompiled application bank as proof that those sources were replayed.

From this directory:

```sh
python3 scout_620_bridge.py
python3 generate_620_leaves.py
python3 reproduce.py --out /data/fresh-spectral-run \
  --foundation-library /data/fresh-complete-application/objects \
  --foundation-library /data/fresh-signed-source/objects
```

The foundation must contain the freshly rebuilt actualGM/actualRamanujan source closure, NicolasBaseline, SourceInterfaces, and kernel LeanCert. `GENERIC_CONTEXT.json` records exact generic library/compiler paths and identities for this host. The complete study bundles the corresponding source/version manifest for a clean environment. No random seeds occur. The strict accepted/rejected CLI routes passed under normal, -O and -OO Python; the final control identity and verified cleanup receipt are in `evidence/controls-cold-v2/`. `reproduce.py` checks that deterministic numerical regeneration produces byte-identical Lean scalar goals, builds every new module in dependency order, and writes actual axiom audits/object hashes. Passing this runner confirms the new-source stack; passing the root source-closure gate additionally establishes the imported sources.

The exact Python discovery routines use rational Taylor/logarithm enclosures, not floating-point acceptance. `scout_620_bridge.py` exports the five exact slab endpoints and conservative c,d rationals. Lean independently proves the resulting inequalities and full actual consumers. Failed610b scouts and failed implementation attempts are retained in the owned evidence directory; they are not primary successes.

## Storage and resources

All scratch belongs to `/data/ivy-rh-limit-20261122/spectral`. Receipts record actual peakRSS, time and artifact hashes. No large prime table, zero list or irreplaceable numerical certificate was created. Do not delete source, accepted proof artifacts or the only reproduction evidence. Small failed-attempt logs/source snapshots are retained. Any later cleanup must be restricted to this owned tree after checking deterministic regeneration.

## Self-contained matched discovery control

Run `python3 matched_transfer_control.py > MATCHED_TRANSFER_CONTROL.json` with its two sibling support scripts and `MATCHED_TABLE1.json`/`MATCHED_TRANSFER_PARAMETERS.json`. Only Python's standard library is needed; a clean directory containing those five files was tested and regenerated byte-identical results. The bundled Table1 rows preserve the exact recorded source hash. The parameter dictionary fixes the threshold, target, intervals, depth, arithmetic precision, polynomial, powers and global barrier; only the old/new proved J transfer changes. `MATCHED_TRANSFER_MODEL.json` maps the constants to the actual source and kernel theorems.

Both outcomes are exact-rational Python exploration, not PV or a Lean certificate. The old fixed lower-envelope recipe does not certify620b. The positive0.001 theorem is a separate five-slab, all-real Lean proof. V2 exports the exact failing old interval and negative fraction, without converting the diagnostic to floating point. The original V1 source and result are retained under `evidence/`; no original outcome is relabelled.
