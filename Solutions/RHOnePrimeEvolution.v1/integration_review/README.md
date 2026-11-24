# Independent final consumer and source-boundary review

This directory reviews the new one-prime integration and three downstream node versions. It is **not** a whole-IEANTN source audit or an optimality/best-known assessment. The scoped written inventory records `(file, declaration, physical LF line)` and source SHA-256, with no collapse by short declaration name.

`FinalConsumerAudit.lean` checks all 24 canonical Solution headliners and the numerical transfer helper `closed_from_numeric`. For each actual compiled theorem it rejects a transitive axiom outside `propext`, `Classical.choice`, and `Quot.sound`, checks an expected provider in the actual proof value, and checks that each required node-input lambda variable occurs in that value. Explicit independently written arrow contracts pin all 24 interfaces. Additional expanded identities pin the CMS input, genuine finite-gap range, one-prime coefficients/onsets, strict endpoints and shifted continuous endpoint. These are checks of the stated conditional theorems; they do not prove the external source predicates.

The corrected negative controls must reject a changed coefficient, an earlier onset, a closed upper endpoint, a finite gap range expanded from 2^64 to 2^65, removal of the numerical node parameter, and removal of the CMS source parameter. Parameter-removal controls pin the graph interface; they do not establish logical independence or necessity of an assumption. For example the numerical node already has its separate closed proof.

## Source boundaries and mathematical applicability

There is no separate Blueprint label for these newly introduced research claims. The correspondence is the exact canonical Conclusions declaration, its generated Challenge contract, and the actual Solution adapter, all enumerated in `SCOPED_DECLARATION_INVENTORY.json`.

1. **`CMSCosineInput.v1.obstruction`.** Its actual body is `IEANTN.RHOnePrimeEvolution.cms616`: ordinary-zeta RH, logarithmic height at least 44, coefficient in [1/2,1], and no prime in the closed forward interval imply the normalized kernel obstruction with additive 29/25. The primary source is CMS, *Fourier optimization and prime gaps*, arXiv:1708.04122v2, Section 6.3 equation (6.16), PDF page 26; the fixed dilation is 0.9, and the source starting point is at least 4·10^18. Logarithmic height 44 lies inside this source range. The interface uses the actual sine integral for J. Source Lemma 7 on page 21 excludes a zero-ordinate coincidence; page 22 discusses removable singularities, and the entire H reformulation follows. The all-parameter removable-value extension, Fourier/L1 identification and derivation of (6.16) are literature-backed/written inputs, not newly formalized here. `analytic/SOURCE_REMOVABLE_EXTENSION.md` states this explicitly. This matters because the resulting theorem is source-conditional, not a Mathlib derivation from RH alone. No unregularized 0/0 quotient is evaluated by this interface.

2. **`PrimeGapTable.v1.gaps`.** Its actual body requires two consecutive prime endpoints p<q with q<2^64 and bounds their natural difference by 1550. Nicely's *First occurrence prime gaps*, 12 August 2019, notes that all gaps below 2^64 have been analyzed, and its maximal-1550 row starts at 18361375334787046697 (PDF https://oeis.org/A000101/a000101.pdf, notes pages 1–4, record page 23; local saved HTML notes and row also checked). The source qualifies the listing as believed complete and verified to the extent practical. The implementation preserves this as a separate historical computation input. Its own terminal-prime Lucas proof and real-variable bracketing/floor transfer are proved, and q≤the proved terminal prime is converted to q<2^64 before using the source. The 1551 strict-open finite window is conditional on this input and requires no RH premise. Neither the historical prime-gap computation nor its completeness is newly verified or source-first PV here.

3. **One-prime ranges/endpoints.** The 0.8768 analytic ray starts at exp(44); its exp(24) extension additionally consumes the finite gap input. The continuous endpoint includes both the argument shift to x+1 and the absolute +2 term. The bounded 0.8357, 0.8512 and 0.8185 results retain their upper bounds exp(110), exp(225) and exp(59), respectively, as well as the exp(24) lower bound and separate finite input. These are actual all-real, both-endpoints-open contracts. None is an asymptotic bound below the older 0.8358 benchmark. The later Blanquer Robles 2026 paper, Zenodo 24429650 Theorem 3, gives coefficient 0.85125 for every real x≥4 under RH; therefore this campaign's 0.8768 ray is not a global record. Its partial Lean bridge is not a mathematical refutation of the paper. Comparison with retunings of its complete functions remains separate from comparing its fixed printed coefficient.

4. **Downstream statements.** `PrimePowerPopulation.v1` consumes the inherited strict octic family; it gives actual open cube-interval counts for all real n≥exp(8), the natural onset n≥2981, and integer powers r≥3. It does not prove a theorem for arbitrary real r>2 or for successive squares. The 0.70 density and its comparison with 0.648 retain the same domain. `Goldbach.v3` leaves its finite binary-Goldbach input explicit and proves multiplicity/range transfers, including more than 750 million sorted triples for every odd n in [6·10^18,8·10^18] given the 4·10^18 finite input. `PrimeQuantile.v4` retains zero-based `Nat.nth` indexing, the full generic/special margins and strict endpoints. These canonical implications do not independently establish the inherited octic family or its analytic source hypotheses. The vacuous change from 2H<n to 2H≤n at even equality is not counted as a range improvement.

No newly discovered mathematical contract error was found in this scoped review. The disclosed source assumptions remain substantive boundaries, not proved facts or numerical execution axioms. Earlier analytic branches and original experimental outcomes are preserved.

## Reproduce the independent final proof audit

After the source-only final closure completes, run from the repository root:

```sh
python3 Solutions/RHOnePrimeEvolution.v1/integration_review/run_audit.py \
  --repository "$PWD" \
  --run /absolute/fresh/audit-output \
  --objects /absolute/final-closure/objects
```

The runner requires the successful fresh compilation receipt. It verifies the plan hash, exact completed module identities, frozen and current source hashes, actual object hashes and compiler hash before loading any final proof object. It compiles the audit against only those application objects and the pinned generic package cache, then executes every negative control. It preserves exact commands, source snapshots, compiler stdout/stderr hashes, elapsed time and per-child maximum RSS. Development `--bank` overlays are explicitly labelled as reused-object checks and never called fresh replay.

Before a writable official hash/native-link build, create experiment-owned exact pinned package copies:

```sh
python3 Solutions/RHOnePrimeEvolution.v1/integration_review/isolate_lake_packages.py \
  --repository "$PWD" --destination /absolute/fresh/private-generic-packages
python3 Solutions/RHOnePrimeEvolution.v1/integration_review/run_official_lake.py \
  --repository "$PWD" --run /absolute/fresh/official-lake-output
```

The package-copy script requires the pinned generic source/cache paths recorded in `LOCAL_CONTEXT.json`; a clean machine must first restore those exact pinned dependencies as described by the campaign reproduction instructions. Copies remain outside publishable source and can be regenerated. The official controller refuses to use the original shared package directories for writable native-link builds. The first attempt's discovered missing generic C-object caches and the corrective isolation are preserved in `CACHE_CORRECTION.json`. An optional `--reuse-core-receipt` explicitly reuses a complete, identical-source earlier ordinary Lake core run; it never presents those modules as newly recompiled.

`run_official_lake.py` separately executes real Lake module builds, the unmodified `ieantn_hash` executable and actual `scripts/ieantn.py fingerprint`/`fingerprint --check`. The ordinary core umbrella includes the original permanent Challenge `sorry` templates. Official bookkeeping success is not actual Solution proof completion; those proof paths are checked separately by `FinalConsumerAudit.lean` and never import the Challenge umbrella.

## Trust and exclusions

These are Lean kernel proof checks. They are not source-first PV, verification of a new C/C++/CUDA numerical program, or exhaustive verification of historical gap/Goldbach computations. Remaining infrastructure trust includes the pinned Lean compiler/kernel/runtime, generic dependency objects, OS and hardware. The external mathematical source predicates are explicit hypotheses, not hidden new axioms. The final source-only compilation, independent proof audit and source-applicability review are distinct acceptance gates.

No new Ramanujan work was performed. No original source, locked input or accepted proof artifact was deleted. Failed development audit evidence is preserved; the exact audit-script corrections are recorded in `REVIEW_NOTES.md`.
