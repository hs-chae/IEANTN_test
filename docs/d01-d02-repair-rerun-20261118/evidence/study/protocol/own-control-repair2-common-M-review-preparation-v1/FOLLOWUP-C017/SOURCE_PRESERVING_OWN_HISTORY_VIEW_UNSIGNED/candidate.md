# D02: explicit arithmetic portfolio

**Status: both families supported for independent mathematical review.**
New proofs use the precise D02 hypothesis plus the pinned common
sources. B0 alone includes the original quasi-Riemann result
Re rho<=7/8 and the verified finite RH height. The added bound
implies Re rho<=27/32 by holomorphic continuation of the
logarithmic derivative, so its effect is not limited to evaluating
psi on x>=e^200. See spectral.md for the exact deduction and
the entire-domain spectral estimates for each cap.


## Latest own-review repair (read first)

The false x-mode Ramanujan lower endpoint has been corrected at
its actual nonpoint-log implementation. The trigger `x 1e70`
is replayed for both inputs with a separate upper enclosure below
1.1. The old code and output history are retained, not accepted
as bounds. The Mertens medium conversion is also conformed to
its written proof, with unchanged certified endpoints.

The additive results and proofs are in **own_repair.md**.
The Ramanujan full-coefficient log onset for order 7 is now
209.48 under D02 versus 249.2 in the matched B0 certificate;
orders 6 through 62 retain full certified tables. The exact
terminal sign ray has the same open endpoint, now isolated to
a bracket of width 1e-32 (B0). For both families the selected
pointwise spectral improvement starts at log x=166.1.
For Mertens and the two related sums the new matched power
bounds at log x>=200 have coefficients .21150 (D02, a=5/32)
and .01218 (B0, a=1/8), with decreasing ratio below .03353.
The extended common sweep and analytic join give coefficient
.07 simultaneously from x=45946496 in the inverse-log units.
The D02 coefficient .22775 yields a separate, longer power ray
simultaneously from x=307; for B0 coefficient .01239 the analogous
onset is x=367949. Uniform power and finite alternatives retain all earlier
tradeoffs. See second_portfolio.json for executable rows and
own_repair.md for the formulas, domains, replay and limitations.

## Previous repair results (retained)

The complete original evidence is retained. The single false
regularity description has been withdrawn: the old R2 function
has a jump at L=32; its inequalities are unaffected. The FKS
Theorem 1.1/1.2 and Corollary 1.4 locator is corrected to PDF p.2.
See repair.md for the review disposition and accounting.

* **Ramanujan:** the terminal sign threshold is unchanged; the
  leading strict quantitative coefficient 1 now starts at L=30.716,
  and the coefficient pair 1+14/L starts at L=47.0194, both in B0.
  The refined spectral layer improves the matched higher-order rays.
  For example the full order-7 profile starts at L=209.7 (D02)
  vs 249.3 (B0); at L=225 the matched coefficients are 1412 vs 847.
  Order 62 is now certified at L=1711.7 vs 2255.7. The refined
  pointwise R1 analytic bound gains strictly from D02 at L>=166.4.
* **Mertens:** D02 gives coefficient .235 from L=166.4 and .21614
  from L=200, with x^(-5/32)/L for P, Q and sum 1/p, and
  x^(-5/32) for the weighted sum. The refined matched B0 coefficient
  at L=200 is .01228 with exponent 1/8; the D02/B0 bound ratio
  is <.0341 and decreases on the entire matched ray. In B0 the
  extended interval sieve and analytic join finish the former
  finite-only .10 branch and certify .082 (in the old inverse-log
  units) simultaneously for all four errors at x>=33901696.
  These finite gains are independent of D02.

The new proofs, closed real onsets, executable certificates and
their limits are in repair_spectrum.md and repair_applications.md.
The earlier, still valid portfolio follows for comparison.

## Original highlights (retained)

* **Ramanujan.** Both inputs give R(x)>0 on the connected terminal
  ray (r,infinity), with r between 38358837682.21792636509053410
  and 38358837682.21792636532336474. The early integer literature
  computation is inherited; the real endpoint is repaired by new
  exact prime counts. The printed real left limit in the later
  Platt–Trudgian theorem is false, for example at 38358837682.1.
  The case R(r)=0 is explicit. Independently of that finite
  inheritance, the new quantitative analytic ray includes
  R>x^2/L^6 for L>=30.74 and R>(x^2/L^6)(1+14/L) for L>=47.04.
  D02 improves the higher-order profiles; for example
  1+14/L+145/L^2+1412/L^3 in these units is certified
  from L=210.1 instead of the common-method sufficient L=249.8.
  At fixed onset L=225, the last coefficient improves from a
  certified 790 to 1412, with proof that the larger coefficient
  is outside the selected B0 profile at that point. The file
  ramanujan.md and portfolio.json retain pointwise and uniform
  profiles, the early margin frontiers and orders through 29.
  D02 does not improve the exact sign threshold.
* **Mertens.** The two relative product errors and the normalized
  prime reciprocal sum error are <.277 x^(-5/32)/L for all
  L>=167 with D02; the normalized log(p)/p sum error has the
  same bound without dividing by L. At L>=200 the coefficient
  can be .234 for each. On that matched whole ray the ratio
  to the B0 simple power bounds with .0132 and exponent 1/8
  is <.035 and decreasing. A separate proof compares the
  finer pointwise envelopes, not just these two choices of
  constants. Both families of sums and both reciprocals retain
  earlier finite gains that require only B0. For example the
  original .2 margin for both products can start at
  2278381.71114184102 instead of 2278382. At the latter onset
  their constants improve to .199961 and .199973.
  See mertens.md and finite.md for the remaining original onsets,
  signed formulas, onsets at fixed coefficients, and whole-ray
  decreasing coefficient branches.

## Review files

* spectral.md: spectral deduction, density/height bounds, real
  smoothing, primitive, analytic-tail monotonicity.
* ramanujan.md: real and integer gap, logarithmic-integral
  approximants, polynomial profiles and complete joins.
* mertens.md, finite.md: weighted transfers and cancellation,
  signed prime-power corrections, old and new envelopes,
  finite and analytic onsets.
* sources.md, source_tables.json: exact original locators and
  tabulations; comparison uses a within-method common reconstruction,
  not a blind baseline.
* attempts.md: tested approaches, repairs and precise limitations.
* profiles.py, mertens.py, intervals.py, certify.py: replay all
  analytic numerical obligations (not a substitute for the proof).
* endpoint.py, finite_mertens.py, finite_joins.py, finite_zoom.py:
  independent finite arithmetic for the applications. Receipts
  have matching scripts. evaluate.py gives selected interval
  profile evaluations, e.g. `evaluate.py log 200`.
* source_audit.py and receipts verify the bound corpus identities.
  None of this is labeled Lean or source-first PV.

The theorems are at the trust tier of the inherited originals
plus the stated (ordinary deterministic, interval) arithmetic
and the new proofs. The spectral margin improvements are
conditional on the additional hypothesis; independent finite
improvements are labeled B0. No use of samples as whole-ray
proofs, no comparison to an outside treatment and no claims of
global optimality or novelty are made.
