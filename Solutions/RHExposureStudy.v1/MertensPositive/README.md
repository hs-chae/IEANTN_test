# Positive first-Mertens bias — Root post-lock synthesis

Open MERTENS_POSITIVE_PROOF.html for the complete offline mathematical proof. The result is the strict lower bound .006/sqrt(x) on the entire closed band [exp24,10^19], with the exact standard full-prime Mertens constant. This is ROOT_POST_LOCK_SYNTHESIS and earns no independent-arm credit.

The final actual Lean theorem is MertensPositive.first_mertens_positive_IEANTN in IEANTNAdapters.lean. FINAL_THEOREM_TYPE.txt contains the compiler's exact type. PUBLICATION_PREMISES.json gives all five retained original-publication predicates and their exact source locators; RH is an additional explicit parameter. All new convergence, finite prime-power, full-prime tail, Abel, definite-integral and elementary numerical steps are proved in Lean. The original BFKNW analytic theorem and zero calculations and Büthe's computations are cited inputs, not formally reverified here. No source-first PV or official Comparator receipt is claimed.

## Reproduce the ordinary Lean checks

SOURCE_MANIFEST.json pins all twelve source modules and their compile order; THEOREM_CENSUS.json and DECLARATION_AUDIT.json cover all27 new declarations by file,name,line. Four unchanged IEANTN statement/data files are included solely for standalone replay; their exact original hashes are in COPIED_IEANTN_SOURCE_PINS.json. No old application object is reused.

Use the generic Lean4.34.0-rc2/Mathlib71a80585 dependencies recorded in BUILD_CONTEXT.json. The actual compiler binary SHA and generic revision are checked. Run `python replay.py --out /a/fresh/replay --optimize normal`. For the other tested modes use `python -O replay.py --out /a/fresh/replay-O --optimize O` and `python -OO replay.py --out /a/fresh/replay-OO --optimize OO`. Each destination must not already exist. The replay copies the exact source closure, creates a fresh object bank, compiles all12 modules and audits all27 declarations; REPLAY_RESULT.json is written atomically only after every route passes. If generic dependency paths differ, provide --context with an explicitly mapped BUILD_CONTEXT.json retaining the exact compiler and Mathlib identity.

The tested final replays are final-normal/, final-O/ and final-OO/. ALLMODE_REPLAYS.json also records18 actual negative CLI controls under all modes. Source identity and validator identity are recorded separately; historical failed attempts and earlier successful snapshots remain preserved outside the minimal source ZIP.

lakefile.toml and lean-toolchain pin a standalone generic project for dependency preparation. The actual checked runs reused only the pinned generic library cache; they do not claim a cold rebuild of Lean or Mathlib, or a recomputation of any original published zero database.

## Render and inspect

`python render_report.py` uses only the included licensed font and vendored latex2mathml3.81.1. The generated HTML is standalone and requires no external math renderer. `python verify_browser.py` repeats the desktop/mobile check with Playwright1.62.0 and its installed Chromium. Browser observations bind the exact HTML hash. These checks have already passed locally; no target-machine action is requested.

## Integration

Use INTEGRATION_PLAN.json. Add the eight new Lean modules to an isolated solution project. When using the full IEANTN package as a path dependency, use its existing byte-identical Buthe/Vocabulary files and do not overwrite them or create duplicate shadow modules. The standalone copied core files remain useful as reproduction inputs. No existing research source, frozen input, worker or Git metadata was changed here; no push was performed.

BFKNW Table13 already contains stronger local positive-bias data on the overlap [exp24,exp29]. This is a whole-band conditional corollary and a checked consumer, with no global priority or optimality claim.
