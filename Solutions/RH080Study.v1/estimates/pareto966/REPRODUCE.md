# Exact 0.9669924 cube coefficient: posthoc kernel completion

The canonical `ThetaCubePopulation.v2` improves the count coefficient from 0.965 to 0.9669924 on the common real ray n ≥ exp(8). The earlier v1 coefficient 0.965 from exp(6) remains unchanged and is explicitly retained as a network dependency. Natural n ≥ 2981 satisfies the new ray. Both prime endpoints n³ and (n+1)³ are strictly excluded.

This is supplemental formal completion of the frozen written discovery, not a retroactive prospective success. The identical 0.9669924 claim was already in the preserved E1/V0 prefix and later in E2/V1. Its completion does not establish a unique advantage for any exposure condition. PROSPECTIVE_ORIGIN.json pins both origins; no original file or outcome is edited.

## Exact analytic inputs and trust boundary

The mathematical input package is unchanged: ordinary RH; Schoenfeld1976 Theorem10, equation(6.1), θ component; and Büthe2018 Theorem2, equations(1.6)–(1.7). In the actual canonical graph these are `RH.v1.hypothesis`, `SchoenfeldRHTheta.v1.refined_theta`, `Buthe.v1.theorem_2_theta` and `Buthe.v1.theorem_2_theta_lower`. There is no standalone Blueprint label for this new project-internal deduction; the canonical correspondence is IEANTN/Nodes/ThetaCubePopulation/v2.

The published source statements are, with inclusive θ(x) = sum over primes p ≤ x of log p:

- Under ordinary RH, |θ(x) − x| < √x (log x − 2) log x /(8π), for x ≥ 2,300,000,000 (Schoenfeld (6.1)).
- θ(x) ≥ x − 1.95√x, for 1423 ≤ x ≤ 10¹⁹ (Büthe (1.6)).
- θ(x) < x − 0.05√x, for 1 ≤ x ≤ 10¹⁹ (Büthe (1.7)).

The original source predicates and primary paper pins are reused unchanged. These published estimates remain source-backed mathematical hypotheses; this work does not verify Büthe's computation or derive Schoenfeld from Mathlib RH alone. All new scalar arithmetic is kernel checked using Taylor, π and rational inequalities, with no native_decide, native execution leaf, sorry or new axiom. This is **conditional kernel mathematics, not source-first C/C++/CUDA PV**. Generic pinned Lean/Mathlib libraries, compiler/runtime/OS and hardware remain the disclosed infrastructure boundary.

## Whole-real proof and endpoint allowance

Write Δ = (n+1)³ − n³ and L = log n. Exact finite prime-sum transport gives

    (Δ − source error at n³ − source error at (n+1)³)/log((n+1)³) − 1 ≤ open cube count.

The added 1 removes a possible prime at the upper endpoint; it is deliberately retained rather than assuming a real cube is composite. No lower endpoint loss is added because θ(n³) already excludes it. The new proof pays this allowance by proving, for every n ≥ 2154433,

    1 < 10⁻⁹ n²/log n.

The exact main term satisfies

    Δ/log((n+1)³) ≥ (1 + 7/(8(n+1))) n²/log n.

For the complete infinite source range n ≥ M, the normalized combined Schoenfeld errors are strictly less than

    (1+1/M)(3L+3/M−2)L /(4π√n).

`polynomial_budget` proves the necessary quadratic/exponential comparison on all real points. Its finite Taylor anchor inequalities establish log(2154433) < 14.5830382 and √2154433 > 1467.7986919. Therefore the last expression is below 0.033007996 throughout n ≥ 2154433. A second whole-ray anchor gives the bound 0.033 for n ≥ 2160000. These are proofs of continua, not sampled evaluations.

Up to n = 2154433, both cube endpoints remain below 10¹⁹: 2154434³ = 9999990391470218504. The actual Büthe inputs give the sufficient coefficient 0.98 there. In the seam 2154433 ≤ n ≤ 2160000, retain the positive main term at n ≤ 2160000. The exact remaining coefficient margin after the endpoint reserve is

    1 + 7/(8·2160001) − 0.033007996 − 0.9669924 − 10⁻⁹
      = 17479603 / 2160001000000000 > 0.

For n ≥ 2160000 the corresponding margin is 7599/10⁹ > 0. This closes the exact frozen 0.9669924 claim while preserving its split points, mathematical sources and original algorithm. The optional written one-source coefficient 0.7436, finite coefficient 0.98868 and additional later-onset constants are not claimed as new Lean theorems here; they are separate original written claims.

## Clean reproduction

Prepare the exact compiler and eight generic package revisions in DEPENDENCY_PINS.json using the repository helper `Solutions/RHOnePrimeEvolution.v1/scripts/prepare_proof_context.py`. The replay independently checks actual compiler SHA/version, package names/order, Git revisions and source cleanliness. Cached generic libraries are explicit dependencies; no earlier application object is loaded.

```sh
python3 Solutions/RH080Study.v1/estimates/pareto966/reproduce.py \
  --repository /absolute/path/to/network \
  --context /absolute/path/to/checked_generic_context.json \
  --run /absolute/fresh/path/pareto_run
python3 Solutions/RH080Study.v1/estimates/pareto966/test_controls.py \
  --context /absolute/path/to/checked_generic_context.json \
  --objects /absolute/path/to/pareto_run/objects \
  --run /absolute/fresh/path/pareto_controls
python3 Solutions/RH080Study.v1/estimates/pareto966/test_validator.py \
  --repository /absolute/path/to/network \
  --context /absolute/path/to/checked_generic_context.json \
  --run /absolute/fresh/path/pareto_validator_controls
```

Repeat the first two commands with `python3 -O` and `python3 -OO` and fresh output paths. The final validator command exercises all three modes. Acceptance uses explicit guards, never assert or __debug__. Atomic RESULT publication requires the complete 18-module source closure and eight-target actual proof-value/input/type/axiom audit, followed by current source/controller hash readback. The five canonical proofs have no axiom beyond the allowed propext, Classical.choice and Quot.sound; some elementary/identity proofs use fewer.

The 18 actual Lean controls check the accepted exact contract, changed unproved coefficient/onset/endpoints, omitted finite source inputs and an ignored source argument. Rejections show proof/type/consumption mismatches; they are not counterexamples to the changed mathematical claims. Fifteen actual CLI guard controls exercise dependency and freshness rejection under normal/-O/-OO.

Each compiler uses two threads and a 32GiB address-space limit, with a 256GiB available-host-RAM admission reserve. Receipts preserve source/object/log/compiler hashes, exact commands, wall/CPU times, maximum per-process GNU RSS, final directory bytes and observed SIGKILL events. Concurrent aggregate RAM peak and exact peak disk are not measured. No random seed or generated numerical dataset is needed. This directory retains compact source/receipt evidence; full accepted private object banks are small and need no large-data cleanup. No source paper, locked evidence or accepted proof artifact was deleted.
