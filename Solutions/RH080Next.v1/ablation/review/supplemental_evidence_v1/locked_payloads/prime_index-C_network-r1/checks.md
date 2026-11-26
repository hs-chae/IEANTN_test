# Check history (live)

- `/bin/lean /work/submission/Transport.lean`, importing only the assigned pack.
  Initial `pc_at_prime` rewrite missed the reducible `primeAt` head in a
  decidable `if`; the attempted replacement `ite_eq_left.mpr` did not
  elaborate. In the accepted route unfold `primeAt`, rewrite by
  `Nat.count_succ`, and simplify with `Nat.prime_nth_prime`.
- First successful run, exit 0: `count_bridge`, `strict_count_bridge`,
  `population_transport`, `combined_cap` each report
  `[propext, Classical.choice, Quot.sound]`. Remaining tasks: uniform
  rank-dependent refinement and exact breakpoint checks.

- Finite-grid proof: a broad `convert` generated irrelevant instance
  equality obligations; replaced by a direct polynomial rewrite.
- Odd spacing: omega saw different atoms for lambda-expanded and named
  prime predicates; a `change` made the nth-prime atoms agree.
- Final `/bin/lean /work/submission/Transport.lean`: exit 0, all nine
  printed dependency lists exactly `[propext, Classical.choice, Quot.sound]`.
  Rational comparisons are kernel arithmetic, not floating-point tests.
