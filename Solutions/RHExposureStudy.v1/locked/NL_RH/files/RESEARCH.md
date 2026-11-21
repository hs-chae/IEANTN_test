# NL + RH research submission index

The explicit unproved hypothesis of all RH results is the exact pinned
Mathlib `RiemannHypothesis`, namely:
```
∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) →
  s ≠ 1 → s.re = 1 / 2.
```
Classical zeta agrees with Mathlib's on
Re(s)>1 by the Dirichlet series and on its continued domain by uniqueness
of meromorphic continuation. When applying RH to a classical nontrivial
zero, the pole at 1 is excluded and the negative even integers are
trivial. The nonnegative-real-part adapter is kernel checked in
RealConsumers.lean; it does not assert RH.

* **PNT.md**: imported baselines, two-box smooth log averaging (B3),
  exact sinc-square moment refinement (B4), parabolic log average (B5),
  signed prime-power removal, integrated-oscillation transfer to the
  exact real pi with the Li2 normalization. Improvement from B5 is
  strict relative to Lee–Nosal B1/B2 on their common log domain >=35;
  the finite Büthe window is explicitly retained where stronger.
* **Intervals.md**: triangular and parabolic logarithmic test functions
  for genuine open prime intervals, including a quantitative count
  beating the stated 22/25 explicit existence width on a finite log band.
  Does not beat CMS's asymptotic gap constant. Also a signed wide-interval
  count and a finite one-sided inverse prime-count example.
* **Weighted.md**: integrated zero kernel cuts the size of the primitive
  error while retaining sign; symmetric and asymmetric Mertens envelopes,
  a coupled signed cancellation without the pointwise psi error, and
  a separate exact low-range audit.
* **Ramanujan.md**: RH-only analytic margin from log x=38.95, lower
  envelope 1+14/L+142/L^2 for L>=60; exact last real crossing; independent
  finite coverage up to 1,630,650,286,564 with G at least 10,786,299 and an unconditional (verified
  height) bridge to exp(665) via centered Logan and Brun–Titchmarsh.
  This extends the specified Johnston finite range, not the
  unconditional asymptotic threshold.
* **FORMAL.md**: layer-by-layer proof and computation status. A source-level
  theorem for the actual Lean quotient sieve and formal local real consumer;
  native evaluation of the large count inputs is separately labeled.
  The C++ finite audit and analytic proof steps are not Lean-verified.
* **comparisons.out**: directed illustrations of margins and two failed envelope extensions.
* **FAILURES.md**, **SOURCES.md**, **SOURCE_REQUESTS.json**: proof-route
  limitations, request/admission metadata and citations.

Reproduce the deterministic arithmetic, object-file type checks, and
native compiled quotient counts with `/bin/bash /work/submission/verify.sh`.
Use optional `RUN_BIG_CXX=1` for the full native C++ finite interval rerun,
and `RUN_NATIVE_DECIDE=1` for the native-assisted Lean endpoint theorem.
Logs of actual completed executions are included. No program in this
packet accesses the network. Main analytic results are unreviewed.


## Reuse with information recovered

The classical integrated formula and the same zero-count discrepancy supply all
three log-window routes, the weighted tail, and the finite-height error transfer.
The parabolic computation uses the same directed trigonometric grid to
certify ordinary absolute moments for Intervals and regularized absolute
Mellin moments for PNT. The signed pointwise pi bound from PNT is used
literally at x and x/e in the RH Ramanujan cells. In Weighted the same
pointwise psi error was kept symbolic until combining the Mertens sums,
and again before comparing a weighted error to the counting error; it
cancels exactly rather than paying two unrelated absolute terms. For the
partial-height Ramanujan proof the centered window retains its half-first
moment, unlike an outer monotone shift whose cost is its entire half-support.
The tiny polynomial residual is formed before interval certification, unlike
enclosing the two large terms independently with a very fine real grid.
