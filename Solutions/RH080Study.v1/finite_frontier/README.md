# Finite prime-interval frontier: complete additive Lean consumers

The new canonical `PrimeInterval.v5` has four source-conditional conclusions:

- Closed upper width1550 for every real 2 ≤ x < 18446744073709551557.
- Strict upper width1550 + ε, for every positive real ε, on the same entire domain.
- Strict width(log x)² for every real 11 ≤ x ≤ exp(42), using the separately named logarithmic-gap source.
- Strict width min(1550 + ε, (log x)²) on 11 ≤ x ≤ exp(42), using both source inputs.

The exact terminal is kernel-proved prime by the inherited Lucas certificate. The range does not extend to every real x < 2⁶⁴. No RH is needed. Existing node versions and all 278 locked mathematical inputs remain unchanged. These are kernel proofs of finite transfers, **not source-first PV or a regeneration of either historical prime-gap computation**.

`PrimeGapTable.v1.gaps` remains the existing external historical-computation input with its recorded completeness qualifications. The new `FiniteLogSquaredPrimeGaps.v1.gaps` is exactly the conventional consecutive-prime claim in CMS arXiv:1708.04122v2 equation(1.15): both endpoints are prime, consecutive, and the lower endpoint p satisfies 11 ≤ p ≤ 4·10¹⁸, with q − p < (log p)². It is a B-tier source input attributed by CMS to Oliveira e Silva–Herzog–Pardi Section2.2. It is not defined to assume any desired all-real interval conclusion and is not presented as a proved closed numerical theorem.

The proofs bracket each real x by consecutive primes p ≤ x < q using a genuine terminal prime. They then apply the relevant source gap bound at p. The logarithmic source applies because 11 ≤ p ≤ x ≤ exp(42) < 4·10¹⁸; monotonicity of log on positive numbers transfers the bound to x. The two conclusions combine by choosing the smaller justified width. The scalar theorem `log_squared_le_iff` additionally proves the exact continuous crossover: for x ≥ 1 and W ≥ 0, (log x)² ≤ W exactly when x ≤ exp(√W). No optimality claim is needed.

The complete application source closure is twelve modules in SOURCE_MANIFEST.json: five exact unchanged inherited modules, two mathematical consumers, a core vocabulary, two node declarations, a canonical proof adapter and the actual `Solution` wrapper. Core vocabulary imports no Solutions. The local source-only replay compiles all twelve from fresh copies, supplies no application objects, checks theorem types/proof values and all eleven headline axiom closures, and also checks the actual inherited terminal-prime/source-gap theorem dependencies. Only propext, Classical.choice and Quot.sound are permitted.

From a clean checkout or compact bundle after the main REPRODUCE.md prepares the pinned Lean4.34.0-rc2/Mathlib71a80585 generic context:

```sh
python3 Solutions/RH080Study.v1/finite_frontier/reproduce.py --context /fresh/context.json --run /fresh/finite-frontier
python3 Solutions/RH080Study.v1/finite_frontier/test_controls.py --context /fresh/context.json --accepted /fresh/finite-frontier --run /fresh/finite-frontier-controls
```

The first command compiled the complete canonical closure in about48seconds with peak child RAM about6.57GiB; no native-execution axioms or proof placeholders occur in the accepted closures. It uses a 64GiB per-child address-space ceiling and reserves256GiB for the host. The second command checks source/receipt identities, repeats the entire source-only closure under Python -O and -OO, rejects18 malformed/reuse routes, and runs four actual Lean negative controls for missing source assumptions and invalid terminal/small-x domains. Negative fixtures intentionally fail and are not proof modules.

The earlier seven-source cold replay and development append are separate historical phases. The complete twelve-source results are the canonical acceptance evidence. No old 300-module object bank is needed for reproduction. Ordinary Lake/Challenge/fingerprint registration is coordinated by the root integration phase; local source-only proof acceptance is separate from official Comparator acceptance.

All code, exact source mappings, pins, commands, typed statements, axiom/proof-value audits and resource receipts are preserved. No large numerical data is generated. Accepted proof objects are retained locally; no original research source or only reproducibility copy is deleted.
