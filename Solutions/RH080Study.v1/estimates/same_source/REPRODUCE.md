# Posthoc completion of the frozen same-source cube argument

This directory completes the exact 0.78146 claim and adaptive equal-cell algorithm in the timely locked `cube-L2_E1_V0-r1`, prefix-0001. The original prospective outcome is unchanged. The origin manifest records the original bytes; this new proof is supplemental posthoc work.

The new canonical consumer is `PrimePowerPopulation.v2`. Its only analytic input is the existing `PrimeInterval.v4.optimized_strict_family`. Its actual upstream ordinary RH, Green explicit-formula, Nicolas and BPT input package remains unchanged and explicit. There is no new Schoenfeld, Büthe or numerical premise. This is kernel checking of a conditional mathematical proof, **not source-first program verification**.

The exact conclusion counts primes strictly between n³ and (n+1)³, for every real n ≥ exp(8). The count is strictly greater than 0.78146 n²/log n. The natural-number onset is 2981. The previous 0.7 result remains available. New canonical v2 files are additive; v1 is unchanged.

## Clean reproduction

Use Lean4.34.0-rc2 and the eight exact generic package revisions in DEPENDENCY_PINS.json. The repository's existing `Solutions/RHOnePrimeEvolution.v1/scripts/prepare_proof_context.py` constructs the small generic-context JSON after preparing those dependencies. The replay independently checks actual compiler bytes/version, package names/order, Git revisions and tracked-source cleanliness. Cached generic Lean libraries form an explicit trusted dependency boundary. No previous application objects are permitted.

From the repository root, substitute absolute paths:

```sh
python3 Solutions/RH080Study.v1/estimates/same_source/reproduce.py \
  --repository /absolute/path/to/network \
  --context /absolute/path/to/checked_generic_context.json \
  --run /absolute/fresh/path/same_source_run
python3 Solutions/RH080Study.v1/estimates/same_source/test_controls.py \
  --context /absolute/path/to/checked_generic_context.json \
  --objects /absolute/path/to/same_source_run/objects \
  --run /absolute/fresh/path/same_source_controls
python3 Solutions/RH080Study.v1/estimates/same_source/test_validator.py \
  --repository /absolute/path/to/network \
  --context /absolute/path/to/checked_generic_context.json \
  --run /absolute/fresh/path/same_source_validator_controls
```

Repeat the first two commands under `python3 -O` and `python3 -OO`, selecting fresh output paths. The third command already exercises normal, -O and -OO modes. No acceptance check uses Python assert or __debug__.

The replay rebuilds all 11 selected application modules from copied source, including the canonical declarations, scalar lemmas, exact interval transfer, finite tiling, canonical Solution, and ten-target proof-value/input/type/axiom audit. It rejects added theta/BW source-provider modules and never reads earlier application objects. The final seven canonical proofs have only propext, Classical.choice and Quot.sound. The complete selected closure is recorded in PLAN.json. The source argument is consumed in the actual proof term, not just listed as a hypothesis.

Each process receives a 32GiB address-space allowance with two Lean threads, subject to a 256GiB available-host-RAM admission reserve. A RESULT receipt appears atomically only after the complete closure succeeds and all current source/controller hashes are reread. Receipts distinguish maximum per-process GNU RSS from unmeasured aggregate peak RAM, and final directory bytes from unmeasured peak disk. There are no random seeds or external numerical datasets.

## Mathematical construction

Let Δ = (n+1)³ − n³ and C₀ = Δ/(3n√n log n). When C₀ ≤ 16 the original Octic frontier applies once to the whole interval. Tight kernel-proved exponential tangent bounds, with an initial log-n slice ending at 8.01, retain the positive lower-order terms and prove the exact 0.78146 constant.

When C₀ > 16, take k = ceil(C₀/16) equal open cells of length Δ/k. The proof establishes that every actual left-endpoint coefficient lies between 1.03 and 16. Their prime sets are disjoint subsets of the original open cube. Summing their actual lower bounds gives a coefficient strictly above 0.789. For log n ≥ 12 the same algorithm gives the additional coefficient 0.804. These stronger branch bounds close the whole real ray; they do not replace the fixed target or algorithm.

The finite scalar reductions are kernel proofs using Taylor inequalities and rational arithmetic. No native_decide, native execution axiom, sorry or new axiom occurs. The exact general family is inherited as a mathematical input; this work does not independently discharge its literature-backed analytic prerequisites or official Comparator approval.

The controls accept the exact contract and reject changed unproved coefficients/onsets/endpoints, an omitted original family, and an ignored source argument. These are proof/type/consumption mismatch controls, **not mathematical counterexamples** to the changed claims.

Preserve the original locked prefix, source code, PLAN/RESULT receipts and accepted proof evidence. All run directories here are small; no large generated prime lists, certificates or numerical arrays exist. Reproduction needs no retained experiment cache. See VERIFICATION_SUMMARY.json and HANDOFF.json for exact hashes and the independent-review status.
