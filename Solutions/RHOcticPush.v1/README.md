# RH octic full-network research campaign (23 November 2026)

This additive research branch starts from `0e2638852a08de84e25f1d179a36356fb12333a5`.
Original experiments, mathematical sources, and published outcomes are preserved.
`BASELINE_THEOREMS.json` freezes the starting theorem contracts before new work.
`PLAN.json` records the authorized project and its acceptance gates.

## First reviewed checkpoint

The `spectral/` GM and Nicolas modules contain completed mathematical proofs,
checked in Lean 4.34.0-rc2 against Mathlib
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`.
These are conditional on the exact named RH/literature inputs in their signatures.
Their proof closures use only `propext`, `Classical.choice`, and `Quot.sound`.
They introduce no native execution leaves, new mathematical axioms, or admits.

* `GMTransport` proves an anchored whole-function compensation bound.
* `GMComparison` retains the old function and proves a strict improvement on the entire ray above exp(24).
* `EvolvedPi` transports that improvement to actual ordinary prime counting.
* `GMPair` cancels the common compensation integral before taking absolute values.
* `NicolasMultipoint`, `NicolasFourPoint`, and `NicolasBlock` prove correlated actual Euler-product inequalities, using nonnegative full spectral weights.

These joint/product results are not a new one-point numerical record. The pair
transfer is a different result from the still-open 0.076 spectral target.
Further research and canonical integration are in progress on this branch.
In particular, do not infer that the fixed 2.15 octic theorem, four full Box
analytic predicates, or finite prime-count source-first verification are complete.
A kernel-checked numerical certificate is not source-first program verification.

`dev_compile.py` is a development check only. Final clean source-reproduction,
source/claim audits, reports and evidence are recorded separately as they finish.
Never run Lake builds into the development overlay: it can contain symlinks to
preserved accepted object banks. Use a fresh experiment-owned build directory.
