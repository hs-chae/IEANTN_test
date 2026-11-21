# Intervals: recovered finite signs and direct spectral counts

Prime counts are \(\pi(y)-\pi(x)\) for \((x,y]\). The DGM symmetric
result below instead has both endpoints open.

## Signed finite count (unconditional with Büthe's computation)

For \(1423\le x\le y\le10^{19}\), Büthe 1511.02032v2 Thm 2
(1.6),(1.7) implies
\[
 \pi(y)-\pi(x)\ge\frac{y-x-1.95\sqrt y+.05\sqrt x}{\log y}.
\]
Indeed \(\theta(y)-\theta(x)\) is at least the numerator, and each
prime in \((x,y]\) weighs at most \(\log y\).
Intervals.lean verifies this on the exact IEANTN functions from the
explicit source predicates and consumes PrimeInterval.v1.Dev.theta_characterisation.
Treating both pointwise deficits as absolute would pay \(1.95(\sqrt x+\sqrt y)\).

For \(x\ge10^8,\ y=x+2.91\sqrt x\le10^{19}\), the count exceeds
\(\sqrt x/\log x\). With \(s=\sqrt x\) the numerator is at least
\(1.01s-2.83725\), while \(\log y\le\log x+2.91/s\) and
\(.01s>2.83725+2.91/\log x\). If \(x=p_n\) with the same endpoint
conditions, then \(p_{n+j}\le p_n+2.91\sqrt{p_n}\) for
\(1\le j\le\lfloor\sqrt{p_n}/\log p_n\rfloor\), with \(p_1=2\).
For nonprime \(x\), an exact or rigorously lower count at \(x\)
can likewise be added to any integer lower bound for the interval.

### Local prime-power subtraction

For a closed Büthe Table 1 row \([b,2b]\) with normalized
\(\psi\)-deficit band \([m,M]\), and \(2\le x<y\) in the row,
\[
 \pi(y)-\pi(x)\ge\frac{y-x-M\sqrt y+m\sqrt x}{\log y}
 -\sum_{k=2}^{K}\left(\frac{y-x}{k^2x^{1-1/k}}+\frac1k\right),
 \qquad K=\left\lfloor\frac{\log y}{\log2}\right\rfloor.
\]
The interval \((x^{1/k},y^{1/k}]\) contains at most
\(1+(y-x)/(k x^{1-1/k})\) integers by concavity, each prime power
contributing at most \((\log y)/k\). For \(K\ge2\) the sum is at
most \((y-x)/\sqrt x+\log K\), by the telescoping bound on
\(1/k^2\) and harmonic integration. This retains the local
prime-power change rather than paying the whole \(\psi-\theta\).
For example on the \(b=2\cdot10^{14}\) row with \(m=-.60,M=.76\),
take \(y=x+2.4\sqrt x\le4\cdot10^{14}\). The count exceeds
\(\sqrt x/\log y\): the slack is at least
\(.04\sqrt x-.912-34(2.4+4)>0\), using
\(\sqrt y\le\sqrt x+1.2,\ \log y<34,\ K<50\).
For existence alone, computed maximal-gap bounds may be stronger.

## Direct DGM RH count

For every \(X\ge e^{40}\) and \(1\le\alpha\le2\), let
\(h=((1/2+\alpha)\log X+.9)\sqrt X\). There are more than
\(\alpha\sqrt X\) primes in \((X-h,X+h)\).
At \(\alpha=1\), width \(3\sqrt X\log X+1.8\sqrt X\) improves the
additive \(4\sqrt X\) in Dudek–Grenié–Molteni arXiv:1503.05403v2
Thm 1.1 on this ray; the source theorem has earlier onset.
CMS Thm 3 has a better asymptotic coefficient; see below.
CMS Thm 5 covers existence from \(x\ge4\), with .88 and a closed
lower endpoint. Applying it at \(x+\epsilon\), and using finiteness
of primes in a bounded enlarged interval as \(\epsilon\downarrow0\),
gives the same upper endpoint for \((x,x+.88\sqrt x\log x]\).

In DGM §3 Eq. (3.1), put \(L=\log X,\ T=\sqrt X/((1/2+\alpha)\pi)\),
\(\beta=hT/X\ge L/\pi\). Then \(T>14.14,\ X>121,\ 0<h\le X/\sqrt3\).
Cutoff equalities can be avoided by taking \(T\) arbitrarily close and
passing to the limit in the continuous scalar bound.
Group \(\sqrt X\log T,\ (3-\log(2\pi))\sqrt X\), and
\(2\sqrt X\log T/(\pi\beta)\le\sqrt X\): the loss divided by \(\sqrt X\)
is at most \(L/2+4-\log(3\pi^2)<L/2+.62\).
The next two normalized terms total
\[
 \frac{2\log(2\pi)}{\pi\beta}+
 \frac{4\log(T/(2\pi))}{\pi\beta^2}
 \le \frac{4+2\pi}{L}<.258.
\]
The \(3X^{1/3}\) term costs \(<.004\) in these units.
All terms containing \(h/\sqrt X\) cost at most
\((L^2+8)h/X\le (L^2+8)3Le^{-L/2}<.001\),
using \(8\log T/(\pi\beta)\le4\) and the
\(\log^2T/\pi+2.05+12\log T/\beta^2\) factor.
The last normalized \(3/(Xh\sqrt X)\) and
\(\alpha\log(1+h/X)\) each cost \(<.00001\).
These ray bounds follow by monotonicity of the polynomial-exponential
factors. Since \(.62+.258+.004+.001+.00002<.9\), the prime weight
exceeds \(\alpha\sqrt X\log(X+h)\). Divide by the largest
possible single weight. This reuses the source's weighted-count
intermediate rather than subtracting two PNT errors.

For long windows \(e^{34}\le x\le y\), the adaptive theta estimate
gives another lower count
\[
 \frac{(y-x)-(A(\log x)+1.01)\sqrt x-(A(\log y)+1.01)\sqrt y}{\log y}.
\]
Take the best valid bound, but endpoint subtraction normally costs
\(\sqrt x(\log x)^2\) for short-interval existence.

## Stronger explicit Fourier count by keeping the interior-prime term

For every real \(x\ge4\cdot10^{18}\) and \(1\le\alpha\le2\), set
\[
 c=\frac{22}{25}(1+2\alpha),\qquad y=x+c\sqrt x\log x .
\]
Then \(\pi(y)-\pi(x)>\alpha\sqrt x\) under RH. This is a second **direct**
route: it uses the actual test function and numerical inequalities of
Carneiro–Milinovich–Soundararajan (CMS), arXiv:1708.04122v2, §6, but
retains an interior-prime contribution rather than assuming that it is
zero. In particular \(c=2.64\) suffices for \(\alpha=1\) on the stated
ray, instead of the symmetric DGM width with coefficient 3 (where the
count is in terms of the midpoint). CMS Theorem 3 obtains an even smaller
asymptotic coefficient \(<2.52\) for \(\alpha=1\), but its statement
does not give an explicit onset. We claim no optimality.

**Scalars and the source inequalities.** Put \(L=\log x\),
\(a=\sqrt{xy}\), \(s=2\pi\Delta=\tfrac12\log(1+cL/\sqrt x)\).
Thus \(x=ae^{-s}\) and \(y=ae^s\).
Use \(F=H(\cdot/.9)\) of CMS §6, \(\widehat F\) supported on
\([-1/.9,1/.9]\) and nonnegative; \(F(0)=1\), \(.83<\|F\|_1<1\),
\(\widehat F(1)\le .885/8\), and
\[
 J(F)=(1-4\int_{[-1,1]^c}\widehat F)/\|F\|_1>25/22
\]
by the numerical facts in (6.11), (6.14), (6.16).
Here and below \(\int\widehat F\) is a Lebesgue integral.
Since \(c\le4.4\), \(\Delta \le cL/(4\pi\sqrt x)<10^{-8}\)
using \(42<\log(4\cdot10^{18})<43\) and monotonicity of \(L e^{-L/2}\).
Hence (6.9) applies unchanged with its normalized constant .070
after multiplying by \(2\pi\). Also \(s<10^{-7}\) and \(a\le2x\).
For the outside primes use the exact inequality preceding the last
line of (6.14), obtained using explicit Brun–Titchmarsh on both sides:
\[
 S_{\mathrm{out}}\le 8\widehat F(1)+4\sqrt a\,s
   \int_{[-1,1]^c}\widehat F+
   24\sqrt a\,s^2\widehat F(1)(.9^{-1}-1).
\]
The last term is \(<.001\): \(\sqrt a\,s^2\le
c^2L^2/(2\sqrt x)\le4.4^2\,43^2/(4\cdot10^9)<10^{-5}\);
even \(24\widehat F(1)/9\le24/9\) suffices. The constant term is
therefore at most .886. This rechecks the source scalar constraint
that was originally used only for \(c\le1\).

For the prime powers \(p^k\), \(k\ge2\), the support fits inside
\([u,v]=[ae^{-2s},ae^{2s}]\) with \(u\ge x/2\), \(v\le2x\),
\(v-u\le5as\le22 L\sqrt x\) (bound the derivative of
\(e^{2s}-e^{-2s}\)). Use the integer-root bound from the finite
interval argument, now with both endpoints included: at most
\(1+(v-u)/(k u^{1-1/k})\) integers. Each term is at most
\((\log v)/(k\sqrt u)\) since \(\|\widehat F\|_\infty<1\).
Thus the power contribution is at most
\[
 \frac{\log v}{\sqrt u}\{(v-u)/\sqrt u+\log(\log v/\log2)\}
 \le 68 L^2 e^{-L/2}<.001.
\]
For the scalar coefficient here use \(\sqrt2<1.5\), \(\log v\le L+1\),
and \(\log((L+1)/\log 2)<L\); the last function decreases for \(L>4\).
The trivial-zero term in (6.5) after multiplication by \(2\pi\)
is \(3\pi\Delta^{-1}(e^{s/.9}/a)^{5/2}<.001\).
Indeed \(e^{s/.9}/a\le2/x\), and
\(\Delta\ge c\log 2\,L/(4\pi\sqrt x)\), using
\(\log(1+u)\ge u\log2\) for \(0\le u\le1\).
All these checks hold also for \(2.63\le c\le4.4\).

**Interior term and contradiction.** Suppose \(\pi(y)-\pi(x)\le
\alpha\sqrt x\). There are at most \(\alpha\sqrt x+1\) primes in
the **closed** interior \([x,y]\), retaining a possible prime at \(x\).
For each, \((\log p)/\sqrt p\le L/\sqrt x\), and
\(|\widehat F(t)|\le\|F\|_1\).
Its total contribution is at most \(\|F\|_1\alpha L+.001\)
(the extra term \(\|F\|_1 L/\sqrt x<.001\)).
Combining (6.5), (6.9), the outside/prime-power bounds and this
interior term yields
\[
 J(F)\sqrt a\,s \le \log(1/s)+\alpha L+1.16.
\]
The error constant is safe since
\((.070+.886+.001+.001+.001)/.83<1.16\).
If \(\vartheta\) of the Mellin formula coincides with a zero ordinate,
apply the bounds at \(c'\uparrow c\) avoiding exceptional ordinates.
The interior count bound remains valid by inclusion in \([x,y]\);
the scalar inequalities pass to the limit. This avoids an
assumption on zeros of a particular ordinate.

Now \(\sqrt a\,s\ge cL/2-c^2L^2/(4\sqrt x)> cL/2-.001\)
using \(\sqrt a\ge\sqrt x\) and \(\log(1+u)\ge u-u^2/2\).
Also \(\log(1/s)\le L/2-\log(c\log2\,L/2)<L/2-3\).
Consequently the left side exceeds
\((\alpha+1/2)L-(25/22)\cdot.001\), whereas the right side is below
\((\alpha+1/2)L-1.84\). This proves the claimed count.
The inherited Fourier and Brun–Titchmarsh steps are published analytic
inputs; the altered interior contribution and validity checks are a
written derivation, not a Lean replay of CMS.
