# A-D02: results and reproducibility

## Main results

1. **Ramanujan:** The optimal strict real positivity ray is \(x>X_*\), where
   \(38358837682.217926<X_*<38358837682.217927\) and \(R(X_*)=0\).
   This uses the admitted QRH but not PsiMajorant; there is also a direct
   contract-powered proof. Both give \(R(x)>x^2t^{-6}(1+14/t)\) for
   \(t=\log x\ge48.75\). At \(t\ge50\) add \(16/t^2\) inside the parentheses
   without the contract, or \(65/t^2\) with it. At \(t\ge220\) and \(t\ge190\),
   respectively, the second-order coefficient can be raised to 145.
   The baseline's literal near-left **real** claim is inconsistent with
   independently checked local prime counts. Its integer restriction is
   used at original trust, then extended using monotonicity.
   Without either QRH or PsiMajorant an independent new range is
   \((X_*,e^{753.8}]\cup[e^{3041},\infty)\); the early and late advances
   over \(e^{58}\) and \(e^{3915}\) are strict.

2. **Mertens:** Without QRH or PsiMajorant, whole-ray coefficient improvements
   hold throughout each original domain. For products and prime reciprocals
   the coefficient falls to \(0.09\) in front of \(t^{-3}\) at \(x\ge20000000\);
   for log-weighted reciprocals it falls to \(0.09\) in front of \(t^{-2}\)
   at \(x\ge35000000\). See the finer table, earlier strict improvements,
   and optimal real baseline-coefficient onset brackets in mertens.md.

3. **Log-free tail mechanism:** By converting the contract to a zero-free
   half-plane and summing the reciprocal zero ordinates against the admitted
   density bound, \(|\psi(x)-x|\le .227x^{27/32}\) for \(x\ge e^{200}\).
   The QRH-only estimate is \(.014x^{7/8}\) for \(x\ge e^{187}\).
   Explicit decreasing coefficients and stronger eventual constants are
   in density.md. Both estimates drive signed power-saving Mertens
   envelopes. Compared with the direct use of the contract, the analytic
   Mertens error terms from \(e^{200}\) onward improve by more than 2753,
   apart from the separately controlled positive prime-power spill.

4. **Further arithmetic:** Improved short-interval lengths, prime counts
   in those intervals, a two-sided explicit maximal totient-ratio bound
   with endpoint cancellation, and prime-square centering of the Mertens
   errors are in tertiary.md.

## Artifact map and status

Selected Ramanujan candidates: density margins with and without the contract
(two source trade-offs), and the non-QRH/noncontract computation in
ramanujan.md. Selected Mertens candidates: the finite-plus-analytic table and
the two density-powered tails. Earlier weaker derivations are retained in
ramanujan.md, mertens.md and qrh.md for audit and premise comparisons.
Original source claims and imported literature computations retain their
paper-level status. No formal kernel theorem or source-first PV is claimed.

Reproduce from this directory with PYTHONDONTWRITEBYTECODE=1 and the
assigned /usr/bin/python3.10 (without -O):
* cert.py — Ramanujan brackets, core, QRH and FKS comparisons;
* density.py — log-free density tails and stronger margins;
* mertens_tail.py — whole-ray analytic comparisons;
* mertens_sieve.py — all finite checks through 268435456, plus the constant
  enclosures, and three left witnesses;
* tertiary.py — short interval and totient comparisons.

All five ran successfully. Scripts use exact arithmetic in assertions.
Floating-point diagnostic displays are not certificate inputs. See notes.md
for limitations and failed trials.
