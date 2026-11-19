# Common spectral transfer

Write \(L=\log x\), \(E(x)=\psi(x)-x\), \(e(L)=E(e^L)e^{-L}\).
B0 is the cumulative original corpus, not full RH; B1 is B0 with
exactly INPUT_CONTRACT.json. Terminating decimal constants are rational.
Set
\[
 b_0=7/8,\quad b_1=27/32,\quad a_j=1-b_j,\quad
 H=3000175332800,\quad h=\log H,\quad \lambda=\frac{\pi}{H-1-\pi/3}.
\]

## 1. Why the new input works before exp(200)

OpenAIQRH Theorem 1.1 (PDF p.4, text lines 255–262) puts the nontrivial
zeta zeros in \(\Re\rho\le b_0\), with equality allowed. FiniteRH
Theorem 1 (PDF p.2, lines 48–52) puts those of positive height at most
\(H\) on the half line. Conjugation supplies negative heights.
There are no real zeros inside \(0<s<1\): the real alternating eta
series is positive there and equals \((1-2^{1-s})\zeta(s)\).

In B1, for \(\Re s>1\) summation by parts of the Euler series gives
\[
 -\zeta'(s)/\zeta(s)=s/(s-1)+s\int_1^\infty E(t)t^{-s-1}\,dt .
\]
The integral through \(e^{200}\) is entire; the rest is holomorphic
on \(\Re s>27/32\) by the exact input, locally uniformly also after
differentiation. Meromorphic continuation gives the identity there;
a zero would cause a pole of the logarithmic derivative. Thus the
new zero cutoff, with its boundary still allowed, applies at ALL
heights and is usable also for \(x<e^{200}\).

## 2. Endpoint bounds
For \(L\ge40\) use FKS Theorem 3.2 (PDF p.8, text 667–681) with
\(T=e^{L/3}\). The admissible tuple is \((40,1/2,0,2.091)\);
\(T>\max(51,L)\) and \(5T+2<e^{L/2}\) at 40 and thereafter.
It gives, for some \(T^*\le2.45T\),
\[
 |e(L)|\le 2.091Le^{-L/3}
       +2\sum_{0<\gamma\le T^*} e^{-(1-\Re\rho)L}/\gamma.
\]
We do not assume that \(T^*\) is independent of \(x\). We use this
theorem, not the older Dudek truncation in FKS Proposition 3.4
whose underlying issues are noted in FKS Remark 3.3.

From FKS Lemma 2.1 with Rosser constants \((.137,.443,1.588)\),
Cor. 2.3 and Table 1 at \(U=100\), the last reciprocal sum without
the exponential factor is
\[
 2\sum_{0<\gamma\le T^*}1/\gamma
 \ \le 1.4+.17(L/3+1)(L/3+2)<L^2/16.
\]
Indeed the coefficient in their \(B_1(U,V)\) is <.17, the log shift
\(\log(10/(2\pi))<.5\), and \(\log(2.45)<1\); take \(V\) tending to
\(2.45T\) from above if needed. Both linear factors are at most
\((1/3+2/40)L\), proving the strict comparison. Thus independently
of density tables we have
\[
 D_j^*(L)=2.091Le^{-L/3}+(L^2/16)e^{-a_jL}\ \ge |e(L)|.       \tag{S1}
\]

For a much smaller bound use FKS **Corollary 2.9**, (2.17), and the
upper half of Table 8 (PDF pp.7–8,26; text 610–632, 3199–3318).
The published conclusion for \(t\ge3\cdot10^{12}\) is
\(N(s,t)\le c\,t^{(8/3)(1-s)}(\log t)^{5-2s}+d(\log t)^2\).
Here is the used subtable, coefficients rounded up; at shared
endpoints the following row may be used.

| s interval | c | d |
|---|---:|---:|
|[.75,.80]|7.798|4.101|
|[.80,.81]|8.162|3.693|
|[.81,.82]|8.538|3.613|
|[.82,.83]|8.927|3.533|
|[.83,.84]|9.330|3.453|
|[.84,.85]|9.747|3.373|
|[.85,.86]|10.176|3.293|
|[.86,.87]|10.620|3.213|
|[.87,.88]|11.076|3.133|

Trust is the stated original corollary, not the unconfirmed .618
half of Table 8, nor recomputation of its parameters. The text of
Theorem 2.7 says \(\delta\ge1\) whereas Table 8 lists about .309.
This apparent parameter discrepancy is not resolved here. Claims
labelled “density-free” use S1 and do not use that corollary.

Put \(A=(8s-5)/3,\ q=5-2s\). No relevant zeros occur below or at \(H\).
Writing \(1/\gamma=\int_\gamma^\infty t^{-2}dt\) and using Tonelli gives
\[
 2\sum_{\Re\rho\ge s,\ \gamma>0}1/\gamma\ \le\
 B_{\rm int}(s)=2c\int_h^\infty v^q e^{-Av}\,dv+
                2d(h^2+2h+2)/H.                            \tag{S2}
\]
For \(v=h+w\), expand \((1+w/h)^q\) through order 4. Its fifth
derivative is negative (\(3<q<4\)), so integration of the polynomial
gives the following upper bound:
\[
 B(s)=\frac{2c h^q e^{-Ah}}A
       \sum_{k=0}^4\frac{q(q-1)\ldots(q-k+1)}{(Ah)^k}
       +2d(h^2+2h+2)/H.                                    \tag{S3}
\]
Order 3 is a lower bound for the **integral expression** S2, not for
the actual zero sum.

Take \(s_i=i/3200,\ i_0=2400,\ n_0=2800,\ n_1=2700\).
Let \(B_i=\min_{i_0\le r\le i}\overline B(s_r)\) where the bar is the
outward upper rational endpoint of S3 computed by bounds.py (BS).
For the jth mesh set \(B_{n_j}=0\) in the following expression
(artificial terminal coefficient, not an assertion of zero density
at \(b_j\)):
\[
 S_j(L)=\sum_{i=i_0}^{n_j-1}(B_i-B_{i+1})e^{-(1-s_{i+1})L},
 \quad D_j(L)=2.091Le^{-L/3}+(L^2/16)e^{-L/4}+S_j(L).         \tag{S4}
\]
Majorize the exponential by its value at the top of each bin,
the last bin being closed on the right. Write the increasing step
function as its first value plus its **nonnegative** successive
increments times the indicators of the upper tails. Bound each tail
by \(B_i\) and collect terms to get \(S_j\). This never subtracts
two upper bounds on actual zero counts. The low real-part zeros
use the \(L^2/16\) bound above, and the formula proves \(|e(L)|\le D_j(L)\).
We have \(D_1<D_0\) for \(L>0\) in these functions: the original has
exactly the additional positive increments from raising the cutoff.

For a stronger whole-domain profile replace \(S_j\) by
\[
 \widehat S_j(L)=e^{-L/4}B_{\rm int}(.75)+
   L\int_{.75}^{b_j} e^{-(1-s)L}
        \inf_{.75\le r\le s}B_{\rm int}(r)\,ds .              \tag{S5}
\]
This follows by writing the exponential on each zero as a constant
plus the integral of its nonnegative derivative up to that zero.
It is no larger than the mesh majorant. The running infimum within a
row is the min of that row's value and the prior left limits (S2
decreases in each row). The integrals admit ordinary positive
quadrature with bounds or S3 order-3/4 brackets; no sampled
interpolation is needed for validity. In particular
\(\limsup_{L\to\infty} e^{a_jL}|e(L)|\le B_{\rm int}(b_j)\):
split the integral at \(b_j-\epsilon\) to see this immediately.
Bounds from S3 are .010444096 and .146302424, respectively, not claims of
optimal constants for primes.

## 3. Finite-height branch and crossings
Let \(C(L)=\lambda+113.67e^{-L/2}\). CH2 Cor. 1.2 (PDF p.3 text
201–245) at \(T=H\) gives \(|e|\le C\) when \(e^L>H\), using
\(1\le y\coth y\le1+y^2/3,\ y=\pi/H\) and
\(\pi/(H-1)+\pi^2/(3H^2)\le\lambda\).
The square-root coefficient is directly checked in bounds.py.
For each \(10^7\le T\le H,\ e^L>\max(T,10^9)\), retain the original
*signed* interval centered at \((\pi/T)\coth(\pi/T)-1\) with radius
\(\pi/(T-1)+c(T)e^{-L/2}\), where
\(c(T)=([\log(T/(2\pi))]^2-\log(T/(2\pi))/3)/(2\pi)\).
Its symmetric counterpart has the additional constant
\(\pi^2/(3T^2)\). CH2 Cor. 1.3 applies on \(x\ge1\), including below \(H\).

CH2 (9.4), PDF p.36, gives for \(34\le L\le58\)
\[
 F_\psi(L)=\frac{(L-2\log(L/(\pi e)))^2-4}{8\pi}e^{-L/2}.    \tag{S6}
\]
The specified \(T=2\pi^2 e^{L/2}/L\) is increasing and is within the
finite-RH domain (check endpoints). FiniteRH Cor. 1 also gives the
\(\psi,\theta\) finite square-root bounds through \(2.169\cdot10^{25}\)
at its respective lower endpoints; PT 2021 Lemma 6 is the real
\(\theta\) version through \(e^{58}\). CH2 Lemma 9.2 (PDF p.35)
gives \(-.751e^{-L/2}\le e(L)\le .791e^{-L/2}\) for
\(10^4\le x\le10^{13}\).

On \(L\ge100\) the ratios \(D_j/C\) strictly decrease: each summand
of \(D_j\) has log derivative at most \(-1/8\), and that of \(C\)
has magnitude less than \(10^{-8}\). Directed evaluations bracket
their unique crossings in (189.023,189.024) for B0 and (168.795,168.798) for B1.
These are crossings of the stated branches, not hypothetical
optimal envelopes. Direct use of the new \(L^2e^{-5L/32}/64\) is
dominated by \(D_1(L)\) for \(L\ge200\): the latter scaled by
\(e^{5L/32}\) is decreasing there and <.3 at 200, versus
\(L^2/64\ge625\). The gain comes from spectral cutoff transfer.

## 4. Integrated error: remove the usual factor 1/a
Define \(K(L)=\int_L^\infty e(u)\,du\), absolutely by S1. The
absolutely convergent identity is
\[
 K(L)=\sum_\rho\frac{e^{(\rho-1)L}}{\rho(\rho-1)}
          -\log(2\pi)e^{-L}
          +\sum_{m\ge1}\frac{e^{-(2m+1)L}}{2m(2m+1)}.        \tag{S7}
\]
To prove it, integrate \(A(s)x^{s-1}/[s(s-1)]\) on \(\Re s=2\)
with \(ds/(2\pi i)\), where \(A=-\zeta'/\zeta\). The absolutely
convergent Dirichlet series can be integrated term by term. The
kernel is \(x^{-1}(x/n-1)_+\) by closing the contour using poles
0 and 1 (at equality it is 0). The integral equals
\(G(x)=\sum_{n\le x}\Lambda(n)(1/n-1/x)\). Partial summation and
\(\sum_{n\le x}\Lambda(n)/n-\log x\to-\gamma_{\!E}\) give
\(G=L-1-\gamma_{\!E}-K(L)\); the normalization follows by adding
the convergent prime-power series to Dusart Theorem 5.7.

Shift first to the vertical line \(\Re s=-2m-1\) for fixed \(m\ge1\).
At arbitrarily large positive and negative heights away from all nearby
zero ordinates by \(\gg1/\log |t|\) the horizontal integrals vanish.
Indeed each interval \([N-2,N+3]\) has \(O(\log N)\) ordinates by FKS's
zero count; remove intervals of sufficiently small reciprocal-log
length to find a height in \([N,N+1]\). CH2 Prop. B.8 (PDF p.46,
text 7337–7394), \(a=1,\sigma_+=2\), gives \(O(\log^2|t|)\) for the
logarithmic derivative uniformly on \([-2,2]\). To the left use
CH2 Lemma A.4 (PDF p.41), Euler convergence for \(1-s\), and the
digamma integral in the proof of their Lemma A.1. The same digamma
integral (bounded kernel) and the cotangent bound \(|\cot(\pi s/2)|\le1\)
on the negative odd vertical line give \(O(1+\log(2m+|t|+2))\) there.
The denominator is at least \((2m+1)^2+t^2\) in magnitude, so the
vertical integral tends to zero as \(m\to\infty\) for \(x>1\).
Zero residues converge absolutely by the count. At 1 the residue
is \(L-1-\gamma_{\!E}\); at 0 it is \((\zeta'/\zeta)(0)e^{-L}
=\log(2\pi)e^{-L}\) by (A.3) (the pole terms and the Euler constants
cancel). At each zero the residue is the negative of that zero's
term in S7. This proves S7 on the real ray, without exchanging a
conditionally convergent unsmoothed formula with an integral.

For \(L\ge\log2\) use
\[
 |K(L)|\le k_j(L)=.047e^{-L/2}+8\cdot10^{-12}e^{-a_jL}
                         +1.838e^{-L}+e^{-3L}.               \tag{S8}
\]
For the low part, subtract CH2 Eq. (B.9) at 0 from its regular part
at 1:
\(\sum_\rho1/[\rho(1-\rho)]=2+\gamma_{\!E}-\log(4\pi)<.047\).
Here \(D(1)=-\gamma_{\!E}, D(3/2)=2-\gamma_{\!E}-2\log2\) for the
digamma function (differentiate the Euler limit for Gamma, and
sum the integer/half-integer harmonic differences). Each summand
has positive real part, since \(\Re(\rho(1-\rho))>0\). For the low
half-line zeros it is positive real and equals \(1/|\rho(\rho-1)|\).
This bounds their contribution by \(.047e^{-L/2}\). The code checks
the numerical constant with the harmonic enclosure of width 1/10000.
For the high part the Rosser count implies \(N(t)\le t\log t/5\)
for \(t\ge100\): the required \(7/8+R(t)\) comparison holds at 100,
and divided by \(t\) its left side decreases while the right side
increases. Tonelli yields \(2\sum_{\gamma>H}\gamma^{-2}\le
4(h+1)/(5H)<8\cdot10^{-12}\). Finally the trivial-zero terms are
bounded by \(e^{-3L}\) for \(x\ge2\). This does not use Table 8.

Further reduce the high term in S8 by taking its minimum with
\(4(h+1)e^{-L/4}/(5H)+S_j(L)/H\) (also with S5), since on the
upper bins \(1/\gamma^2\le1/(H\gamma)\). Leave the two elementary
terms of S7 as a signed center if desired. In particular the
limiting coefficients in S5 multiplied by \(1+1/H\) bound the
scaled product and prime-sum errors: the low terms vanish in that
limit; high \(K\) costs at most \(B_{\rm int}(b_j)/H\).
