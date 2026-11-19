# Reproduction, attempts, and remaining bottlenecks

## Operational record

First non-login bash command printed the requested working directory;
its second instruction, `ls /task/INPUT_CONTRACT.json
/task/RUNTIME_PATHS.json`, failed with **exit 127: ls: command not found**.
Subsequent shell glob/path output and `/usr/bin/python3.10` reads
confirmed both files and read the permitted offline materials. Bash
also reports a nonfatal `LC_ALL: cannot change locale (C.UTF-8)`.
This was not a packet or mathematical execution failure.
No outside corpus, processes in other sessions, or private review
beyond the supplied own D01 review/referral were used. Source identities
of all seven PDFs and text extracts were matched against
`SOURCE_INDEX.json`. The proof locators use original PDF page indices
rather than treating extraction symbols as independent premises.
The controller records usage; there is no inferred operation/token count.

## New replay

Run in `/work/submission`, with non-login /bin/bash and assertions enabled:
```sh
/usr/bin/python3.10 -B -u claims.py early rays orders
/usr/bin/python3.10 -B -u localgap.py
/usr/bin/python3.10 -B -u mnew.py
/usr/bin/python3.10 -B -u mfinite.py
/usr/bin/python3.10 -B comparison.py
```
The analytic modules inherit outward signed integer arithmetic
in `verify.py`: its Taylor, logarithm, and prime count verification
are explained in `certificates.md`. Powers of rational endpoints
in the new gap minorant are evaluated **as exact fractions**
before enclosure, rather than pre-rounding their reciprocals.
All displayed float formatting in the receipts is for display,
not a decision rule. `mfinite.py` consumes the validated
D01 intervals for the normalization constants; the independent
source for those intervals is the D01 sieve as documented in
`certificates.md`. It does not consume any assumed new numerical
data. The prefix for `localgap.py` uses the independently
checked D01 root counts (`verify.py root`). The D01 large sieve is
not rerun merely to retest the inherited entirety in D02.
The D01 claim registry and review are included intact;
nothing in the D02 attempts deletes a supported D01 row.

In the candidate scripts any explored candidate with a missing
cell or analytic slack is not admitted by the documents.
A `False` or failed exploratory assertion is a failure of that
particular cap, not a counterexample to the arithmetic statement.
Use the exact claims and receipts in the final tables.

## Serious attempts and concrete limitations

* Directly inserting the D02 (psi) bound at (e^{200})
  diminished the asymptotic exponent but retained its large
  logarithmic allowance. It neither moved the useful onset
  before 200 nor improved the comparison around the constant
  CH2 floor. Recovering a **global** strict half-plane by
  Mellin continuation fixed the onset issue. A single uniform
  density envelope solved log removal but gave a weaker
  Mertens coefficient .33348 in the (5/32) units at log 170.
  Piecewise layering (2) reduces the checked coefficient to
  .298101889 there. We used only the 0.77 first subtable,
  not the preliminary alternative subconvexity constant.
* With the same improved zero-strip bound, absolute Abel
  summation still lost a substantial factor at both Mertens
  weights. Treating the FKS cutoff (T^*) as constant in the
  integration variable would not be justified. The infinite
  high-strip approximation and controlled residual solve
  this rigorously; the (1/H) factor in the exact integrated
  kernels arrives without dropping any jumps. The residual
  lower strip and large-ordinate tail are both enforced
  at every real (x). Reducing the limiting power-shape
  coefficient significantly would now need either improved
  density near the right edge or genuine phase cancellation
  in that weighted zero sum, not a tighter absolute Abel kernel.
  The coefficient .160 at log 1240 failed (computed cap
  .160042859365); the rounded certificate at 1250 passes.
* In the moderate Mertens range the finite-height CH2 floor
  and (C_T/sqrt{x}) term are independent of the new tail.
  Height optimization, separate product signs, finer log
  cells and a small-(x) finite extension improve B0. They
  do not close the drop from the last inherited finite cap
  .010 to the larger finite-height-derived cap at the
  final sieve join. E.g. the specific combined CH2 cell cap
  near log 26 is .050233705..., not .0500. Improving that
  join further needs finer oscillation data or a much
  longer independently audited segmented sum. The existing
  envelope has no hole at the join.
* In the early Ramanujan gap, the exact finite counterexample
  already fixes the last positivity boundary. Small positive
  margins around the true boundary use a new short
  certified interval; one cannot infer a uniform quantitative
  constant over the large unsieved remainder of the finite
  bridge merely from its inherited sign. Analytically,
  improving the prime-power correction and enlarging CH2's
  height set helps most around the loss of the one-sided
  sign assumption. The candidate .30 ray at log 39.666
  failed with the certified cusp budget; 39.67 works.
  At log 36.52 the improved analytic sign certificate is
  still negative, not a true counterexample. The exact
  inherited positivity theorem covers that point.
* For higher gap orders, retaining only the leading term
  in a rescaled tail comparison failed even for the
  (M_1) target: the `k=1` test at 199 dropped the
  positive (145/t^2) term, giving a negative bound.
  Scaling by the next order repairs it. Initial large-order
  tests also lost precision when an interval reciprocal was
  rounded before multiplication by a large factorial.
  Exact rational monomials and a certified 48-term
  barrier fix the specific table joins. For genuinely
  arbitrary order, an anchor at fixed log 1 costs a
  factorial-sized initial error and fails to give the
  desired linear onset. Moving the anchor to half the
  target argument makes the initial error exponentially
  smaller and yields the all-order theorem.
* A more optimistic asymptotic exponent is not validated
  for either family. A shift cancellation cannot simply
  be assumed: in the exact gap expansion the coefficient
  of the shifted normalized counting error tends to 1 and
  the unshifted coefficient to -2, not opposites of equal
  magnitude. The one-sided recurrence converse is a
  stronger affirmative obstruction than a failed numerical
  search. Similarly changing the 7/8 in the original QRH
  proof to 27/32 would require new family estimates, since
  the assumed zeta control says nothing about the
  extremizing Hecke character used in its Part II.
  Published-source envelopes are cumulative; no
  global optimum over all possible proofs or conjectural
  logical independence is inferred.

## Restart state

Both new families have complete proof/finite/tail joins and exact
replays, ready for independent review. Inherited proofs and their
trust are distinct from new D02 research. Next review priorities:
verify the boundary inclusion and FKS Table 8 weights in (1)–(4),
the high-strip Laplace integration and two prime-power signs in
(6), the joint shifted domain of (8)–(9), and the two converse
Mellin identities. Remaining improvements are the actual analytic
bottlenecks above (not an unclosed join in a claimed row). No
full Lean, compiler-verified source PV or independent blind
baseline is a deliverable here.
