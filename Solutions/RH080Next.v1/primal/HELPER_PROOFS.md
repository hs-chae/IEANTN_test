# Actual analytic helper proofs

These are kernel-proved mathematical bridges, separate from source-first PV of
numerical programs. All accepted theorem closures have only `propext`,
`Classical.choice`, and `Quot.sound`; no native execution axiom or admitted proof
is accepted.

`ActualArithmeticSplit.actual_full_arithmetic_wing_bound` is the module entry;
the declaration is `RH080Next.Primal.actual_full_arithmetic_wing_bound`. It
bounds the actual `CMSPrimeIndex` weighted von-Mangoldt series by the exact
central half-open finite prime sum, both exterior positive wings, and the actual
nonprime absolute sum. Its only external input is the existing general
Montgomery–Vaughan source proposition. The precise physical prime sets, their
logarithmic coordinates, weights and endpoint assignments are proved rather
than supplied as an interval-cover oracle.

The two wings together have allowance
`(2*Q*d*exp(L+R*d)/log(ell))*positiveLeak(W) +
(4*Q*ell/log(ell))*nodalH`, with the actual source weight
`Q=(L+R*d)/exp((L-R*d)/2)`. The central interval is
`(exp(L-d),exp(L+d)]`. For `L=t+d`, this is exactly the central interval used by
the unchanged explicit-window geometry. The lower central endpoint belongs to
the left exterior prime set; the upper endpoint belongs to the center.

The proof consumes the genuine finite-atomic continuous BV theorem, a proved
finite Lipschitz bound, exact positive variation on every aligned refinement,
and exact exterior positive-area integrals. Left-wing reversal is proved by
positive/negative variation and telescoping. It never charges an error for each
mesh cell and never assumes a merged-component count.

`ActualPrimePowerAllowance.actual_nonprimeMangoldt_lt` (the declaration is in
`RH080Next.Primal`) proves convergence and an actual nonprime weighted-family
sum below0.001 on the entire continuous domain `t>=42`, `1/2<=c<=1`, support
radius at most10 and height bound at most2. The proof counts integer roots in
the narrow interval for each exponent, bounds the number of exponents, and uses
`Lambda(p^k)=log(p)`. It does not count every prime power below the upper endpoint
or assume a numerical prime-power bound.

`AffineDerivativeBounds` proves the actual derivative tail envelope
`abs(F'(u)) <= (R*V1+2*V0)/(2*pi*u^2)` for nonzero `u`, including cancellation and
all endpoint jumps. The separate all-real derivative/continuity lemma is in
`../explicit/ExplicitAffineDerivative.lean`.

The complete combined arithmetic closure was freshly rebuilt from45 sources,
with only pinned generic dependency objects reused:

```sh
python3 Solutions/RH080Next.v1/primal/reproduce_actual_wings.py \
  --context /absolute/path/to/clean_proof_context.json \
  --out /absolute/path/to/fresh-owned-run
```

The accepted run took148.24 seconds and its largest measured process used
3,943,136 KiB RSS. Exact source/object hashes, commands and metrics are in
`evidence/ACTUAL_ARITHMETIC_WINGS_COLD_RESULT.json`. Smaller independent replay
scripts and receipts are retained for the derivative, positive-cell area,
positive variation, Lipschitz, wing-BV and prime-power components. The final
explicit-prime theorem is assembled in the separate explicit lane; these helper
proofs alone do not assert that every original numerical source program or its
full application consumer has been migrated to source-first PV. Official
Comparator approval is absent.
