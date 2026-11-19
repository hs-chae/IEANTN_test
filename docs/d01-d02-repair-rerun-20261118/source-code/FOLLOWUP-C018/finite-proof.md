# Finite Mertens certificates and their analytic join

This file justifies the ordinary executable integer certificate in finite.c. It does not assert PV or formal semantics of a compiler.

Let N=20,000,000, K=1,000,000 and Q=2^56. Use Eratosthenes up to N, striking multiples p^2,p^2+p,... of each surviving p up to sqrt(N). A composite n has a prime divisor at most sqrt(n), hence the unstruck n>=2 are exactly the primes.

**Exact log enclosures.** For a ratio x/y>=1 used by the program, factor out 2^k to put z=x/(2^k y) in [1,2), let t=(z-1)/(z+1), and use
\[
 \log z=2\sum_{j\ge0}\frac{t^{2j+1}}{2j+1},\qquad 0\le t\le1/3
\]
(by integrating the geometric series). For the normalized part, use the lower Q-fixed-point integer for t, use lower products for t^2 and recursively for its odd powers, and take lower quotients for the first 31 terms (odd degrees 1 through 61). The fixed-point t^2 has error <2/Q. The odd-power recurrence thus propagates error at most (1/9) times the previous error plus (5/3)/Q, so the odd-power error stays <2/Q, starting from <1/Q. The terms including the division each lose <3/Q. The omitted tail at t<=1/3 is <1/Q even after the factor 2. The normalized log thus differs from the computed lower by <256/Q, as does the similarly computed log 2. All k are <=25 (checked); 16384 units is sufficient outward slack for their linear combination. For log log x, feed the lower and upper fixed log bounds back into the increasing log routine with denominator Q. All calls have arguments at least 1. Divisions with outward ceilings and floors, and sums and products on the integer scale, are exact. No C runtime libm evaluation is used. The fixed-size integer proof uses that all represented logs are <18, all harmonic and prime sums and their enclosures are <64 (use \(\theta(t)\le2t\) and partial summation for the weighted sum) and positive initial scaled accumulators fit 64 bits; signed differences fit int64. The wide products of two uint64 values, and denominators used in the power sums, fit unsigned 128 bits. The program requires the ordinary GCC unsigned 128-bit extension.

**Constant intervals.** For gamma, use
\[
 H_K-\log K-\frac1{2K}\le\gamma\le H_K-\log K-\frac1{2K}+\frac1{K^2}.
\]
On each interval [k,k+1], trapezoidal error for 1/t is positive and at most \(\sup |(1/t)''|/12=1/(6k^3)\) by integrating the linear interpolation error; sum and pass to infinity. Integral comparison makes the given 1/K^2 ample. Enclose \(H_K\) by summing reciprocals downward, allowing K units of upward slack.

For \(p\le N\), sum the nonnegative terms \(1/(j p^j)\) for \(j\ge2\) while \(p^j\le Q\), each rounded down, and allow one unit per term and two for the omitted geometric tail. Similarly sum \(\log p/[p(p-1)]\) over \(p\le N\) using the lower logs, one division-rounding unit and \(\lceil16384/[p(p-1)]\rceil\) per prime. The upper prime tails are **not** taken from the decimal approximations in Dusart:
* Let \(u=\log N\) and \(\delta=.001\). Dusart 4.2 gives \(|\theta(t)-t|\le\delta t\) for all \(t\ge N\) by the .2/\(\log^2 t\) row, since \(16.8<u<16.82\). Thus partial summation gives
\[
 (1-3\delta)/N\le\sum_{p>N}\log p/p^2\le (1+3\delta)/N.
\]
The factor changing this sum to the first weighted prime-power tail is at most \(1+1/N\); use the wider interval \([.997,1.004]/N\).
* For the other tail, \(\sum_{p>N}1/(2p^2)\) is within
\(\delta(3+1/u)/(2Nu)\) of \(\int_N^\infty dt/(2t^2\log t)\), by parts with weight \(1/(2t^2\log t)\). By integrating by parts once, this integral is between \((1-1/u)/(2Nu)\) and \(1/(2Nu)\). The remaining powers multiply the upper by at most \(1+2/N\) (sum a geometric series). With the log bracket this gives \([1.38,1.50]\cdot10^{-9}\). All threshold numerical conditions follow by elementary integer calculations and the log enclosure above, or by the verified Decimal checks.

Combine with \(\gamma\) to enclose \(M\) and \(B_3\) at common denominator Q. The program prints the endpoints, and they can also be used to give pointwise enclosures for any finite prime-sum calculation. No table of tabulated values of the constants is assumed.

**Covering cells, strictness, and witnesses.** The prime sums are right-continuous constant between primes. On every \([p,p_{\mathrm{next}})\), use the current sums, using the *upper log at the next prime* too, which safely bounds the open interval and its left limit there. On the last cell include N and truncate the first cell used at 100000. At an actual prime, checking with the post-jump prefix provides the bound. For products the log of the normalizing \(Q\) ratio is \(\sum_{p\le x}(1/p+\sum_{j\ge2}1/(j p^j))-\log\log x-\gamma\), computed using the same positive prefix method, not an empirical error or the unsigned error for the other product. Differences are enclosed at both ends of each cell using monotonicity of log and log log. If \(v\ge0\) and \(v<1/1002\), \(e^v-1\le v/(1-v)\le 1.001v\) and \(1-e^{-v}\le v\). The integer product bound is rounded upwards with that exponential multiplier only on the appropriate sign, interchanging signs for \(P\). Multiply by the upper endpoint \(L^3\) (or \(L^2\) for the weighted sum) via outward fixed-point multiplication, proving both the claimed non-strict domain and inclusion of nonintegers. If this fails to certify a cell, record its upper endpoint. In the end all later cells are certified, so the last recorded endpoint is a sufficient onset including that point. Rows 0,1,2,3 are the reciprocal sum, normalized \(Q\), weighted sum, normalized \(P\). Shared onsets in the statement simply take the maximum of the three applicable columns.

The optional witness test uses an inward lower bound for the exact absolute error at the *left input* of a cell. For products whose log is bounded away from zero by \(v>0\), both absolute errors are at least \(v-v^2/2\): \(e^v-1\ge v\) and \(1-e^{-v}\ge v-v^2/2\). Multiply by true lower bounds on the log powers. Only report if the lower rounded product strictly exceeds the target. Thus the reported witnesses are true violations of the given constants at those inputs, whereas a last unproved cell is not evidence of a violation. For the newly tighter coefficients, actual witnesses explain why they cannot be uniformly moved back to the original thresholds. For the old .20 and .30 rows this computation does not improve the original cutoff; those published bounds are retained unchanged.

Finally the finite rays cover up to N while §5 of candidate.md supplies every indicated analytic join starting below N, with outward-cell and monotone-tail proofs. The finite original proofs near the large Ramanujan sign threshold are separate; this sieve is not an attempt to reverify those much larger finite ranges.
