# FOLLOWUP-D02: complete two-family candidate

The only new premise is INPUT_CONTRACT.json. Original papers and the own validated D01 floor remain cumulative. D02 implies the zeta cap beta <= 27/32 (allowing equality), and the converse to the exact premise is proved using the original formula. No stronger Hecke or Dirichlet assertion is imported.

## Main conclusions

* **Ramanujan.** Preserve the exact open real sign ray and least strict integer onset 38358837683. The new B0 proof gives unit normalized margin from log x = 42.471, and the two-term factorial profile from 47.02. Under D02 the eventual strict degree-6 profile holds from 186.54 rather than 220.37, degree 32 from 887.63 instead of 1158.51. At log-onset 201 the coefficient of the same exponential exact-Li loss L^4 exp(-L/8) drops from .060 to .00161. Retain all bounded intervals, premiums and arbitrary-order profiles in d02_gap.md.
* **Mertens and prime sums.** At L=200 the common power coefficient drops from .018221 to .000495 at rate 1/8, or .25594 at the stronger rate 5/32, without a log-square loss (divide by L as well for the products and reciprocal sum). Finite joins give .003358 at rate 1/8 from x=15000000 for all four errors under D02. Keep the signed intersection, stronger/nondominated powers, earlier onsets and direct/density-free variants in d02_mertens.md. Secondary B0 improvements include the fixed .2 product onset 2278381.72 and .3 weighted onset 912559.9975.
* **Comparison.** This compares with the explicit original-only portfolio, keeping every assessed D01 theorem. Both applications additionally prove that matching the new exponential rate over B0 would itself prove the stronger zeta exclusion. No unproved separation of deductive closures, global optimality, or blind baseline is claimed.

## Evidence map and ordinary replays

| file | role |
|--|--|
| d02_analysis.md | exact assumption, continuous density, signed primitives, source locators |
| d02_gap.md | real sign, finite joins, margins, factorial and exact-Li profiles |
| d02_mertens.md | both products and sums, pointwise envelope, whole-ray comparisons |
| d02_cert.py, run_d02.py, d02_checks.log | final analytic and finite receipt obligations |
| optimize_d02.py, optimized.log | compared settings and certified factorial tails |
| finite_d02.py, finite_d02.log, finite_extended.log | prime-cell proofs through 66 and 300 million |
| power_new.py, power_new.log | power-scale finite bridge through 24154954 |
| common.md, ramanujan.md, gap_repair.md, mertens.md, spectral_repair.md, tradeoff.md | unchanged D01 proofs |
| OWN_D01_VALIDATED_FLOOR.json, D01_M_REVIEW_review.json, D01_M_REVIEW_review.md | inherited claim registry, exact identities and review |
| attempts.md, RESTART.md | failed tests, remaining limits and review handoff |

From this directory, use PYTHONDONTWRITEBYTECODE=1 and:

    /usr/bin/python3.10 optimize_d02.py
    /usr/bin/python3.10 finite_d02.py
    /usr/bin/python3.10 finite_d02.py --extended
    /usr/bin/python3.10 power_new.py
    /usr/bin/python3.10 run_d02.py

The final driver reads the named receipts. The generator outputs can be redirected to fresh files and compared. Published computations and the validated D01 source and ordinary replay retain their original trust tiers. Source-first PV / full analytic Lean: neither claimed. Independent review of D02 follows this candidate stage.
