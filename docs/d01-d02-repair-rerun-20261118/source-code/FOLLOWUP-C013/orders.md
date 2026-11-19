# Arbitrary fixed order: explicit algorithmic rays \(B0\)

For each integer \(j\ge 0\) let \(g_j\) be the true Li-profile coefficient
\[
 g_j=\sum_{r=0}^{j+4}\left(r!\binom{j+4}{r}-r!(j+4-r)!\right).
\]
Then for every real \(x\ge \exp(a_j)\),
\[
 L^6 x^{-2}R(x)>\sum_{k=0}^j g_k/L^k ,
\]
where \(a_j\) is the explicitly terminating integer algorithm in
`orders.py`. This general construction is for higher orders, not
a substitute for the sharper small-order onsets in the table.

Positivity: divided by \(n!\) with \(n=j+4\), the formula is
\(\sum_{s=0}^n1/s!-\sum_{r=0}^n1/\binom nr\).
At \(n=4\) it is \(1/24\); at \(n\ge 5\) the second sum after
removing the two ends is at most \(2/n+2(n-3)/(n(n-1))\le  .6\),
whereas the first sum after removing its first two terms is at
least \(1/2+1/6\). The first four formal pre-profile coefficients
are zero, as in the finite polynomial of `ramanujan.md`.

For a certified infinite-domain check at general order, now use
\(S_N(t)=\sum_{i=0}^N i!/t^{i+1}\) with \(N=j+6\).
For \(f=e^{-t}\operatorname{Ei}(t)\) as before,
\[
 f(t)-S_N(t)=e^{1-t}(f(1)-S_N(1))
          +(N+1)!\int_1^t e^{u-t}u^{-N-2}\,du .
\]
Here \(|f(1)|<3\) from the convergent series and the bounded
constant at zero. The integral over \([t-1,t]\) is at least
\(e^{-1}/t^{N+2}>1/(4t^{N+2})\). On \([1,t/2]\) it is at most
\(e^{-t/2}\). On \([t/2,t]\), differentiating \(e^u/u^{N+2}\)
for \(t\ge 4(N+2)\) bounds it by \(2/t^{N+2}\).
Thus the initial two integer checks in the loop guarantee
\(S_N(t)<f(t)<U_N(t):=S_N(t)+4(N+1)!/t^{N+2}\)
on \(t\ge a\). They use \(e^{-v}\le2^{-\lfloor v\rfloor}\) and
the decrease of \(t^{N+2}e^{-t/2}\) and \(t^{N+2}e^{1-t}\)
from \(a\). For \(G(t)\) one also needs the lower barrier at
\(t-1\). Accordingly the returned log onset is the certified
\(a\) below; the first two barrier tests must be made at \(a-1\)
(and the start of the search ensures the monotonicity there).
Use \(tU_N(t)<2\) by the third integer check at \(a\).

As before, retain only terms through degree \(2(N+2)\) (unscaled)
in the lower expansion of \(S_N(t-1)/t\), and subtract \(U_N(t)^2\).
This polynomial agrees with the formal Li gap through \(g_{j+1}\),
since the coefficients there cannot reach the last upper term or
require factorial terms beyond \(N!\). Subtract the target, multiply
by \(t^{j+1}\), and drop positive decaying terms, bounding negative
ones by their values at \(a\). This gives the quantity `low`.
The prime-counting terms are dominated by `v4`, with 4 in place
of 2.08 as the linear coefficient in the upper square. The whole-ray
monotonicity argument in `ramanujan.md` applies with \(k=j+1\).
The rational envelopes `V` upper-bound these errors at \(a,a-1\)
by the elementary power of 2 comparison. If `low>E`, every real
\(t\ge a\) is covered. Along the doubling sequence all barrier
checks eventually hold and the two final quantities approach
\(g_{j+1}>0\) and 0, respectively. This proves termination as
well as validity; it is not a search for a conjectured estimate.
