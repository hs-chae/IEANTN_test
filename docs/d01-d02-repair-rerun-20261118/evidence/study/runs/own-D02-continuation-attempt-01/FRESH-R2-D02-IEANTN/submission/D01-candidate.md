# Reviewed-ready research portfolio: FOLLOWUP-D01

**Main conclusion about the treatment.** With all seven supplied
originals available, D01 is implied by the common originals.
In fact on every real \(x\ge e^{200}\) they imply
\(|\psi(x)-x|<.021\,x^{7/8}\), versus D01's
\(x^{7/8}(\log x)^2/64\). The proof combines the original QRH
zero-free half-plane, explicit FKS density and Perron bounds,
and verified finite RH. This establishes equality of deductive
strength on every matched domain, not merely a tie between
selected applications. Both family statuses therefore refer
to **no additional improvement from D01**, not to a failure to
improve the published arithmetic conclusions.

## Secondary results using the common originals

* **Ramanujan gap.** The exact real strict-positivity ray is \(x>r\),
  where \(38358837682+.21792636<r<38358837682+.21792637\) and \(R(r)=0\).
  Nonnegative at this endpoint; the least integer onset is 38358837683.
  This joins inherited finite computations to a new explicit
  analytic tail. It also repairs the literal real endpoint of
  the printed Platt–Trudgian early range.
  For \(G(L)=L^6 R(x)/x^2\), the portfolio includes \(G>.20\)
  on \(L\ge36.99\), \(G>1\) on \(L\ge43.16\),
  \(G>1+13.69/L\) on \(L\ge49\), stronger bounded-domain
  tradeoffs, higher coefficients, and computable full rays
  for every fixed Li-profile order.
* **Mertens products and sums.** The original thresholds are retained.
  New finite certificates start at \(100000\); they join at
  \(195730000000>e^{26}\) to analytic bounds. For instance,
  from \(x\ge50000000\) the relative product errors and the
  normalized prime-reciprocal residual are at most \(.057/L^3\),
  and the weighted-prime residual is at most \(.062/L^2\).
  From \(L\ge200\) the corresponding bounds include
  \(.191x^{-1/8}/L\) and \(.190x^{-1/8}\), with smaller coefficients
  at later onsets. Signed transfer formulas and a pointwise minimum
  retain the stronger branches through all intermediate regions.
  The constants and original normalizations are specified in the proof.

## Files and trust

- `density.md`: full-range implication of D01, sources and proof.
- `ramanujan.md`, `gap-results.md`, `orders.md`: statement, finite join,
  analytic pointwise and polynomial profiles, arbitrary-order algorithm.
- `mertens.md`: raw products, both prime sums, finite/analytic joins,
  signed envelope and comparison at matched onsets.
- `certificates.md`: executable replay commands, interval/sieve
  correctness arguments, failed attempts and remaining bottlenecks.
- `verify.py`, `mcheck.py`, `orders.py`, `tables.py`, `sieve.cpp` and
  the result receipts are submitted with exact hashes.

The new certificates are ordinary exact computations, not Lean or
source-first PV. Inherited original-paper results retain their stated
trust and hypotheses. No independent blind B0 run or independent
mathematical review is claimed by this submission.
