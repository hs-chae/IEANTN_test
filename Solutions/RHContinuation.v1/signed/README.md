# Signed RH continuation: exact results and reproduction

This is a supplemental mathematical continuation. Historical exposure outcomes and the original `RHExposureStudy.v1` are unchanged. `PV` is reserved for actual source-first program verification; none is claimed for these new kernel-only proofs or native Arb scouts.

The completed same-input first-Mertens result is `first_mertens_positive_cube_IEANTN` in `source/CubeProfile.lean`: the actual prime sum minus `log(x)+E` exceeds **0.014/sqrt(x)** throughout **exp(24) <= x <= 10^19**, replacing the old 0.006 on that exact band. The same five original BFKNW/Büthe source statements and RH remain explicit. Squares and omitted cubes are regrouped and bounded, with exact finite Abel summation and continuous-range inequalities; no new numerical data are inserted. `MertensProfile.lean` also proves **0.00031/sqrt(x)** from exp(21). The nonconstant profile is retained. BFKNW's numerical inverse-zero-square mass remains literature-backed, not independently source-first verified.

`NicolasBaseline.lean` installs the stronger **known** full Nicolas proof function (Eq2.19, x>599), using exact analytic beta and the actual prime product. Its actual spectral sum carries a summability guard. This is literature import and normalization, not a new record.

The genuinely different Mobius work is under `mobius/`: actual sums of mu(n) and mu(n)/n. A new written RH method proposes `|M(x)| < 1100000*x^(107/132)` for all real x>=1 and gives the weighted consumer `6908000*x^(-25/132)`. The Hadamard/zero-count/Poisson/Gamma analytic chain is independently reviewed written mathematics, **not completed Lean**. Seven source-only modules kernel-check its scalar estimates, actual finite smoothing, uniform strip scalar comparison, three-explicit-integral conditional consumer, and weighted Abel transfer. Read `mobius/RESULTS.json` and actual printed theorem types for the open analytic obligations. A source-first PV result is not claimed.

`caption-source/Table13OtherColumns.lean` and the original `source/Table13Check.lean` give source-independent literal-caption counterexamples for four of BFKNW Table13's five columns. These do not reject the underlying numerical data under a corrected normalization and do not affect the separate BFKNW154/21 inputs used by the 0.014 theorem.

## Reproduce from a clean Linux x86-64 checkout

Use the campaign commit recorded in the root report, with its exact `lean-toolchain` and `lake-manifest.json`. Install that Lean toolchain and restore the **manifest-pinned** generic dependencies/cache; do not run an unpinned `lake update`. The compiler SHA and all nine dependency source revisions are checked by the scripts. No historical application `.olean` is used in the full signed or seven-module Mobius replays.

From the network checkout, after restoring its generic Lake dependencies:

```bash
work=$(mktemp -d)
python Solutions/RHContinuation.v1/signed/prepare_context.py \
  --core "$PWD" --compiler "$(elan which lean)" --out "$work/context.json"
python Solutions/RHContinuation.v1/signed/reproduce.py \
  --context "$work/context.json" --out "$work/signed-normal"
python -O Solutions/RHContinuation.v1/signed/reproduce.py \
  --context "$work/context.json" --optimize O --out "$work/signed-O"
python -OO Solutions/RHContinuation.v1/signed/reproduce.py \
  --context "$work/context.json" --optimize OO --out "$work/signed-OO"
python Solutions/RHContinuation.v1/signed/mobius/reproduce.py \
  --context "$work/context.json" --out "$work/mobius-normal"
python -O Solutions/RHContinuation.v1/signed/mobius/reproduce.py \
  --context "$work/context.json" --optimize O --out "$work/mobius-O"
python -OO Solutions/RHContinuation.v1/signed/mobius/reproduce.py \
  --context "$work/context.json" --optimize OO --out "$work/mobius-OO"
```

Every output directory must be fresh. Each replay copies and hashes the complete selected application source closure, compiles from source using only the pinned generic libraries, checks every declared theorem's axioms, and publishes its atomic result only after all gates pass. `THEOREM_CENSUS.json` keys identities by source file, physical LF line and full declaration. The scalar and Mobius component package's successful status explicitly preserves its analytic gaps. Standard logical axioms are `propext`, `Classical.choice`, `Quot.sound`; no native execution axiom is accepted.

The actual CLI acceptance controls are `exercise_controls.py` in each package (69 signed and 36 Mobius cases across normal/-O/-OO). Their current embedded context is the recorded machine context. For a relocated environment, make a disposable copy of the package, replace only its `BUILD_CONTEXT.json` with the generated context, then execute that copied controller with a fresh `--out` directory. Each source corruption, missing child, duplicate JSON key, wrong mode and unknown option must fail closed.

The three canonical node adapters are `Solutions/{Nicolas,MertensRH,MobiusRH}.v1/Solution.lean`; their Lake projects point to these exact shared source directories. They prove only their listed transport conclusions. MobiusRH's proposed power remains `none-yet`, and its weighted adapter inherits that open upstream proof. Official Comparator workflow receipts are not fabricated.

## Directed numerical formula comparison

Lean reproduction requires no Python-flint. The optional source-formula comparison uses Python-flint0.9.0, 256-bit directed Arb. Exact wheel hashes are in `mobius/PYTHON_FLINT_PYPI_PIN.json`; the Linux x86-64 wheel is pinned by `mobius/requirements-linux-x86_64.txt`. In a fresh Python>=3.10 environment install that hash-pinned requirement, then run:

```bash
python Solutions/RHContinuation.v1/signed/mobius/compare_frontier.py \
  --out "$work/frontier.json"
```

`MATHEMATICAL_FRONTIER.json` retains full RZA, all seven actual JLT output rows, all fifteen full Lee–Leong coefficient profiles, and both the full and parameterized Simonic RH functions on their exact source domains. The proposed function is strictly active at the checked logarithmic points132 through10^7; the known Simonic full function wins at10^8. The crossing sign bracket is40443820..40443821, without a uniqueness claim. Kernel-only comparisons prove the full RZA comparison for every log(x)>=132 and the actual JLT headline comparison for every log(x)>=200. Neither comparison proves the pending M bound itself.

The native Arb quadrature scout is `mobius/scout_arb.py` with its preserved source pin/receipt. It found that naive high-height quadrature is expensive and did **not** verify the complete26-million-height integral. The analytic method removes that quadrature leaf; eight sample panels are not promoted to a full certificate.

## Evidence and storage

`VERIFICATION.json`, `SOURCE_MANIFEST.json`, `THEOREM_CENSUS.json`, `FINAL_AXIOMS_AND_TYPES.txt` and `receipts/` record exact current evidence. New Mobius evidence has its own parallel files. Primary source URLs/versions/hashes are pinned; full copyrighted research copies are retained locally for audit and are regenerated by download rather than bundled as claimed original results. Research transcripts and unrelated workspaces are excluded.

The accepted proof artifacts and essential sources are retained. Large temporary material was not generated in this track; selected obsolete build-object copies can be regenerated from the exact sources. Any cleanup is limited to verified experiment-owned temporary directories, with source/log/receipt preservation and an explicit deletion inventory. No original research input or only reproducibility copy is removed.
