# Finite Mertens audit and common improvements

All results on this page are B0 results. All four stated
coefficient comparisons are strict on their closed real rays.
The product and reciprocal sum coefficients are in units 1/(log x)^3;
the log p/p sum coefficient is in units 1/(log x)^2.

## Compared with the original margins, at their original onsets

* At x>=2278382, the two product coefficients can be .199961 (P)
  and .199973 (Q), respectively, rather than .2.
* At x>=2278383, the reciprocal sum coefficient can be .199917,
  rather than .2.
* At x>=912560, the weighted sum coefficient can be .29999948,
  rather than .3. At x>=1000000 it can be .295973.

Fixing the original coefficients instead, the following earlier
real onsets suffice (rounding the upper root enclosures upwards):

| Error | coefficient | safe closed real onset |
|---|---:|---:|
|P |.2|2278381.575555466|
|Q |.2|2278381.71114184102|
|sum 1/p|.2|2278382.113038|
|sum log p/p|.3|912559.997437|

These are not integer endpoint substitutes. The near-onset
root brackets in zoom_run.txt also prove failure at the lower
side of each bracket; the normalized error crosses a continuous
piece. All later prime/slab endpoints are accounted for.
If both products are wanted with the same .2 margin and
the same onset, use the Q row.

## Coefficient/onset tradeoffs

Here are sufficient closed *real* onsets per error (or take the
maximum for the four together). More rows in portfolio.json.

| C | P, Q | sum 1/p | sum log p/p |
|---:|---:|---:|---:|
|.25|1514831|1514831|1520747|
|.22|1526521|1526687|2275993|
|.199|2278421|2278421|3455719|
|.195|3451297|3451297|3457591|
|.18|3458977|3458977|3470287|
|.17|3461921|3461921|4994051|
|.165|3470353|3470353|4994723|
|.16|3474797|3474797|5001907|
|.15|5001809|5001809|7105289|
|.14|7105289|7105289|7125263|
|.13|7125263|7125299|8788723|
|.12|8789189|8789189|12878431|
|.11|12894433|12894487|not joined at the finite onset|

Other validated comparisons at fixed onsets include:
at x>=4000000, (.159819,.159826,.159845,.171440);
at x>=6000000, (.140077,.140082,.140096,.150051);
at x>=8000000, (.122904,.122908,.122920,.131942);
at x>=9000000, (.119594,.119597,.119605,.127220).
Analytical tail coefficients from u=17 (hence also x>=25000000)
are <.117, so these rows and all C>=.12 finite joins cover the
whole ray. For the additional .11 row the first three errors
use the sharper U_0 tail argument in mertens.md. In contrast
the .10 sweep results and the .11 weighted result were not
joined by this original sweep alone. They are now joined by
the additional 60-million certificate in repair_applications.md.

## Proof of the finite checks

The deterministic Eratosthenes sieve goes to 25000000, marking
multiples beginning at p^2 through floor(sqrt LIMIT); it includes
1565927 primes (see sieve digest in finite_run.txt).
The four cumulative quantities are obtained by multiplying
p/(p-1), adding 1/p and adding log(p)/p; use intervals
enclosing those three followed by the indicated normalization.
There is no rounding of primes, no random prime tests, and no
use of a sampled grid of large x.

Here are details of the normalizer intervals:
* For gamma start with H_N-log N-1/(2N)+1/(12N^2), N=20000.
  Its excess over gamma is in [0,1/(20(N-1)^4)]. Indeed for
  f(t)=1/t on each cell [k,k+1], set z=1/(2k+1).
  The excess of the trapezoid over the integral is
  2 sum_(j>=1) [2j/(2j+1)] z^(2j+1).
  The derivative correction (f'(k+1)-f'(k))/12 is
  (4/3) z^3/(1-z^2)^2. The leading coefficients match;
  each later correction coefficient is larger, and their
  aggregate excess is <=5z^5 for k>=N. Sum with
  z<1/(2k), telescope the trapezoids and derivatives,
  and bound the tail by an integral.
* Compute the initial prime sums defining M and B3 through
  Y=25000000. The remaining weighted B3 tail has main term
  -log(1-1/Y). For its decreasing weight f(t)=1/(t(t-1))
  in the Stieltjes integral against theta, the absolute error
  from this main integral is at most
  delta(Y)[2Yf(Y)+integral_Y^infty f],
  where delta(Y)=.2/(log Y)^2 by Dusart Table in Theorem 4.2,
  valid for all t>=Y. For the M tail f(t)=
  (-log(1-1/t)-1/t)/log t. Bound its main integral between that
  of 1/(2t^2 log t) and that integral times 1/(1-1/Y);
  bound the two endpoint terms using 2Yf(Y)<=1/((Y-1)log Y).
  The alternating geometric integral through terms 14 and 15
  rigorously encloses the main integral as in mertens.md.
  These operations give the intervals in the receipt, without
  taking published decimal M,B3 approximations as exact.

Between successive prime events the error signs can change,
but the normalized *signed* functions multiplied by u^3
(or u^2) are monotone. For the P signed function use
d((c u-1)u^3)/du=u^2(4c u-3) with c u=1/Qhat>.75.
For Q use d((c/u-1)u^3)/du=u(2c-3u) with Qhat<1.5.
For the reciprocal sum use u^2(3(error_signed)-1);
for the last sum use u(2(error_signed)-u).
The code checks guards .8<Qhat<1.3, reciprocal signed error
<.1 and weighted signed error <1 at both ends for x>=10000.
Since each unscaled function is monotone on a prime slab,
the guards and hence these derivative signs hold throughout.
Thus the maximum modulus is at one of the two endpoints,
including the *left limit* at a prime and the actual value
at the prime separately. This proves full slab coverage;
the additional queried nonprime threshold values and root
brackets are handled the same way.

finite_run.txt reports the last endpoints not certified at
each threshold. Any next prime from finite_joins.py and both
sides of every later prime pass, so all slabs from that next
prime pass. There may be a better onset inside the preceding
slab, as demonstrated by the zoom. Endpoints printed to nine
decimals are rounded up by interval arithmetic. The certificate
requires the standard Decimal correctness for exp and ln,
and normal interval arithmetic; it is not a source-first
formal proof of program execution.
