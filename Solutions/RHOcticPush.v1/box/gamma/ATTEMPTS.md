# Rejected development attempts

All rejected receipts/stdout remain in owned /data/ivy-rh-octic-20261123/box-gamma-*.
No failed source is admitted by SOURCE_FREEZE.json.

* Euler-v1/v2/v3: local membership-to-inequality elaboration, a rational inverse
  simplification, rewriting all occurrences of rpow_one, lambda beta reduction,
  and the RCLike.re/Complex.re wrapper. Euler-v4 passes actual beta/Jacobian proof.
* Quadratic-v1/v2: numeral exponent normalization and elementary grouping of a
  rational product. Quadratic-v3 passes with explicit scaling algebra.
* Damped-v1: same real-projection wrapper and a pointwise function subtraction.
  Damped-v2 passes with an explicit integral projection calculation.
* Mellin-v1: an unnecessary tactic after a reflexive rewrite, overly eager congr
  splitting of a commutative product, function-uncurry inference, and reducibility
  of IntegrableOn. Mellin-v2 passes product integrability and both final roots.
* LSP was called before tactics and after edits. It sees generic first/fourier
  modules, but cannot load newly compiled gamma imports until the owned developer
  overlay is linked. Explicit pinned compiler commands with stated object banks
  supplied actual accepted diagnostics in the meantime. No application premise
  was introduced to repair this tooling limitation.

No mathematical premise, integral domain, numerical output or original source
was changed by these fixes. No OOM event or bulk numerical artifact occurred.

* Scaling-v1 lacked explicit lambda reduction; scaling-v2 passed.
* Actual-box-series-v1 mistakenly invoked the filter-level Tendsto.congr API
  through the HasSum abbreviation. Replaced by genuine HasSum.congr_fun; v2 passed.
* H-series-v1/v2/v3 rejected local cast types, function-composition reduction,
  positivity on a lower-bound goal and a rational denominator not factored for
  field_simp. Factored denominator (2N+1)(2N+3); v4 proves the actual harmonic
  finite sum and full series value.
* Factorization-v1..v5 rejected PNat-to-Nat inference, reducibility/coercion of
  real/complex powers, and a final reflexivity goal. Actual factorization itself
  already passed in v3; v6 additionally passes actual zeta identity. No desired
  moment value was inserted.
* First-moment-v1 rejected a pointwise-function normalization and Complex.re
  cast rewrites; v2 proves the original complete predicate with no arguments.
