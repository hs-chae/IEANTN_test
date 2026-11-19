# Mertens products and both prime sums: real envelopes and tradeoffs

For real \(x>1,\ L=\log x\), put
\[
 C_P=e^\gamma L\prod_{p\le x}(1-1/p),\quad C_Q=1/C_P,\quad
 E_1=\sum_{p\le x}p^{-1}-\log L-M,\quad
 E_{\log}=\sum_{p\le x}(\log p)/p-L+B_3 .
\]
Here \(\gamma\) is Euler's constant,
\(M=\gamma+\sum_p[\log(1-1/p)+1/p]\) and \(B_3=\gamma+\sum_p\log p/[p(p-1)]\), as in Dusart 5.6–5.7. The cutoff includes primes at equality. "First three" refers to \(|C_P-1|,|C_Q-1|,|E_1|\); the fourth is \(|E_{\log}|\). A polynomial coefficient bounds the four errors on scales \(L^3,L^3,L^3,L^2\); a power coefficient of rate \(z\) bounds them on scales \(Le^{zL},Le^{zL},Le^{zL},e^{zL}\). All numerical coefficients below are strict on closed real rays. Take the pointwise minimum of all valid branches below and in the entire inherited floor.

## Power envelopes and their comparison

**B0:** common rate-\(1/8\) coefficient **.01908** from \(L=14\), and also from \(x=104000\). From \(x=100000\) use .01908 for the first three and .02080 for weighted; from 70000 use .01946 and .02138. These are new B0 certificates, not D02 improvements.

**B0+D02, common coefficients at the same closed onset \(L=14\):**

| rate | 1/8 | .130 | .135 | .140 | .145 | .150 | 5/32 |
|:--|--:|--:|--:|--:|--:|--:|--:|
| coefficient | .01111 | .01191 | .01278 | .01920 | .04461 | .10363 | .2973 |

At rate \(1/8\), the earlier onsets \(L=13,13.5\) permit .01677,.01363. Later \(L=15,16,17,18,19.03\) permit .00741,.00498,.003358,.002275,.001537. The last two also work from \(x=40000000,150000000\), by finite joins explained below. Results at matched late onsets:

| log-onset | B0, rate 1/8 | B0+D02, rate 5/32 | B0+D02, rate 1/8 |
|--:|--:|--:|--:|
| 170 | — | .29473 | .001453 |
| 180 | — | .27903 | .001007 |
| 200 | .018221 | .25594 | .000495 |
| 250 | .015899 | .22294 | .00009021 |
| 300 | .014652 | .20535 | .00001742 |
| 500 | .012654 | .17733 | \(2.904\cdot10^{-8}\) |
| 1000 | .011454 | .16057 | \(4.305\cdot10^{-15}\) |
| 3000 | .010761 | .15079 | \(2.906\cdot10^{-42}\) |
| 30000 | .010476 | .146743 | convert from rate 5/32 |
| 1000000 | .010446 | .146320 | convert from rate 5/32 |

The first three errors gain the denominator \(x^{5/32}L\) instead of \(x^{1/8}L\), the weighted error \(x^{5/32}\), with **no** log-square loss. At the *same* rate \(1/8\) and onset 200 the coefficient drops by a factor greater than 36. On \(L\ge170\), .29473 at the new rate beats all B0 **uniform power rows** retained here on their matched rays, because \(.29473 e^{-170/32}<.01044\), below those B0 coefficients, and the ratio decreases. The weighted bound there is also \(<c=1.048\cdot10^{-12}\) and decreases, and its polynomial-scale comparison is \(<.043\) at 170 and decreases. These are comparisons of certified bounds, not lower bounds on the true errors.

D02 rate-\(1/8\) coefficients on earlier closed rays:

| real \(x\) onset | first three | weighted |
|--:|--:|--:|
| 100000 | .01895 | .02080 |
| 104000 | .01724 | .01876 |
| 180000 | .01469 | .01598 |
| 250000 | .01363 | .01469 |
| 400000 | .01104 | .012001 |
| 500000 | .01020 | .01103 |
| 700000 | .00849 | .00919 |
| 1000000 | .00807 | .00870 |
| 1200000 | .00753 | .00816 |
| 1500000 | .00737 | .00793 |
| 2000000 | .00608 | .00654 |
| 2500000 | .005752 | .006141 |
| 4000000 | .004622 | .004957 |
| 5000000 | .004340 | .004675 |
| 6000000 | .004047 | .004335 |
| 8000000 | .003549 | .003809 |
| 10000000 | .003456 | .003676 |
| 15000000 | .003358 | .003358 |
| 40000000 | .002275 | .002275 |
| 150000000 | .001537 | .001537 |

For fixed tolerance .01111 the first-three onset \(e^{14}\) is improved to 400000, and the weighted onset to 500000. At fixed 104000 the new .01724/.01876 improve the B0 .01908 for both groups. The finite prefixes use no D02 information: the improvement in completed rays is the changed large-\(x\) tail.

**Crossovers.** The ratio of \(K_2e^{-z_2L}\) to \(K_1e^{-z_1L}\) for larger \(z_2\) is decreasing, with unique crossing at \(\log(K_2/K_1)/(z_2-z_1)\); the \(1/L\) cancels for the first three. The .2973 rate-\(5/32\) profile crosses .01908 at \(1/8\) in \(87<L<88\); versus .001537 at \(1/8\) the crossing is in \(168.47<L<168.48\). Only compare where both are valid. Against Dusart's .2 or .3 polynomial coefficients compare \(KL^2e^{-zL}\), maximizing at \(2/z\). For .2973 the ratio decreases on the original matched domains and starts above target; the crossings are \((53,54)\) at .2 and \((50,51)\) at .3. For .01908 at \(1/8\) it starts above target below 16, then crosses on the decreasing side in \((40,41)\) and \((34,35)\), respectively. All comparisons are directed endpoint tests with the stated derivatives, not sample plots.

## B0-only polynomial and finite improvements

At fixed .2, the real onset for both products is **2278381.72** (Dusart 2278382; inherited repair 2278381.8); both also satisfy .199997 from 2278381.75 and .199973 from 2278382. At .2 the simultaneous first-three onset is **2278382.12** (inherited 2278382.2). At 2278383 both products satisfy .199879 and the reciprocal sum .199917. For the weighted sum .3 holds from **912559.9975** (Dusart 912560, inherited repair 912559.998), and .29999946 from 912560. These are real sufficient onsets, not rounded or minimal. The non-strict originals are Dusart 5.6, 5.7, 5.9 (PDF pp.17–20, onsets 2278383, 912560, 2278382 respectively); retain them on precisely their domains.

New common analytic polynomial coefficients are .117 from \(L=17\), .104 from 17.3, .079 from 18, .057 from 18.8, .047 from 19.25 and .043 from 19.5. These and the following finite joins hold already over B0, without FKS Cor. 2.9.

| real \(x\) onset | first three | weighted |
|--:|--:|--:|
| 15000000 | .09574 | .10246 |
| 18000000 | .09394 | .10059 |
| 20000000 | .08875 | .09479 |
| 25000000 | .08810 | .09334 |
| 40000000 | .07019 | .07483 |
| 50000000 | .05620 | .06036 |
| 60000000 | .05609 | .05910 |
| 150000000 | .04467 | .04709 |
| 200000000 | .043 | .043 |

Use finite_d02.log to 66000000 and the .079 analytic tail for the rows through 25000000; use finite_extended.log through 300000000 and the .043 tail afterward for the other rows. This preserves the earlier \(10^7\) and below branches from D01. The longer finite test does **not** pass the .057 tolerance at 60000000 for the weighted sum (upper .059093); a shorter finite join would not have sufficed for that target.

## Analytic proof of the coefficients

Use \(D_Q=\log C_Q,\ A(t)=\sum_{n\le e^t}\Lambda(n)/n-t+\gamma,\ K(t)=t^{-1}+t^{-2}\). Define the nonnegative tails
\[
 U=\sum_{p\le x,\ p^m>x,\ m\ge2}(mp^m)^{-1},\quad
 T_0=\sum_{p>x,\ m\ge2}(mp^m)^{-1},\quad
 V=\sum_{p^m>x,\ m\ge2}\log(p)/p^m.
\]
Partial summation of the end-inclusive weighted \(\psi\) sums and the original limiting normalizations give
\[
 D_Q=u(L)/L-\int_L^\infty uK+U,\quad E_1=D_Q+T_0,\quad
 E_{\log}=u(L)-\int_L^\infty u+V,\quad 0\le U\le U+T_0\le V/L.
\]
The exact derivations and the alternative θ-only identities with **no** prime-power corrections are in mertens.md. Use (B) of d02_analysis.md for signed \(\psi\) integrals, with \(J=Z_b+2e^{-L}\). For \(\theta\), the correct spectral interval is obtained by subtracting the signed prime-power interval for the full integral, not by using unshifted (B).

**Early improvement of the square and cube tails.** Let \(N=e^{29}\). On \(1\le y\le N\), \(\theta(y)\le y\): verify at every prime up to 121 by directed logs (and empty beginning), then use CH2 Lemma 9.2's \(\psi-y\le .791\sqrt y\) and Dusart Prop.4.3's \(\psi-\theta\ge .9999\sqrt y\). Globally \(\theta(y)\le1.000058y\) by CH2 Cor.1.3 for \(y\ge N\). On \(1\le y\le N\) a lower deviation bound is \(\theta(y)-y\ge-2.415001\sqrt y-1.78y^{1/3}\) by the CH2 \(-\sqrt2\) lower \(\psi\) estimate and Dusart Cor.4.5. For \(j=2,3,\ y=e^{L/j}\),
\[
 V_j:=\sum_{p^j>x}\log(p)/p^j
       =-\theta(y)y^{-j}+j\int_y^\infty\theta(v)v^{-j-1}\,dv .
\]
For \(10\le L\le58\), use that lower bound at \(y\le N\), and the upper \(\theta(v)-v\le0\) for \(v\le N\). Beyond \(N\), use \(\theta(v)-v\le cv+113.67\sqrt v\). This gives
\[
 V_j\le \left[\frac1{j-1}+2.415001y^{-1/2}+1.78y^{-2/3}\right]y^{1-j}
 +\frac{jc}{j-1}N^{1-j}+\frac{j\,113.67}{j-1/2}N^{1/2-j}.
\]
For \(m\ge4\) split at \(w=e^{L/4}\). For \(p\le w\) the remaining geometric tail per prime before log weighting is at most \(2/x\); for \(p>w\) use \(p^{-4}/(1-1/w)\) and drop the negative summation-by-parts boundary. The resulting bound is \(1.000058[2+\frac43(1-1/w)^{-1}]e^{-3L/4}<3.46e^{-3L/4}\) for \(L\ge10\). Sum these three upper bounds for \(V_+\) (Vplus in code). CH2 Lemma 9.2 (PDF p.35, LF5216–5244) has the stronger signed \([-.751,.791]e^{-L/2}\) local \(\psi\) interval on \(10\le L\le29\), since \(10^4\le e^{10}\) and \(e^{29}<10^{13}\).

On that band, \(W=.791e^{-L/2}+(1+1/L)J+V_+\) bounds \(L|D_Q|,L|E_1|,|E_{\log}|\); the tails are nonnegative and \(.751\le.791\). In each requested scale the four bounds follow from \(W e^{W/L}\) multiplied by \(e^{zL}\) or \(L^2\), using \(e^w-1\le w e^w\). On \([10,29]\), \(W/L\) decreases; after power scaling each nonconstant term decreases, and for polynomial scaling each decreases from \(L\ge17\) (smallest decay at least \(1/8\)). Constant terms of \(V_+\) are scaled at the right endpoint 29. The endpoints and small prime check are in run_d02.py / d02_cert.py.

**Middle joins and tails.** On \([29,58]\) use the B0 bound \(W_*=(L^2/(8\pi)+1.25)e^{-L/2}\) with factor \(e^{W_*/L}<1.0001\) from the proof of spectral_repair.md §3. Its scaled bounds decrease. On \([58,B]\) use the CH2 floor and the inherited tail bound
\[
 W=c+115e^{-L/2}+4.1\cdot10^{-12}e^{-(1-b)L},\quad
 V\le\widehat V(L)=(1+7e^{-L/4}+3d)e^{-L/2}+3.8e^{-2L/3},
 \quad d=c+114e^{-14.5}.
\]
For \(W\) use \(|u|\le c+113.67e^{-L/2}\), (B) and \(\widehat V\); check the coefficients at 58. Scale the floor \(c\) at \(B\); the other scaled terms and exponential factor are bounded at the left. For the fixed-power joins take \(B=188.5\) over B0 or \(B=168.6\) over B0+D02. Beyond \(B\) use \(W=D_b(L;.75,k)+(1+1/L)J+\widehat V\) with \(k=.275\). The later table uses \(k=.275,.25,.225,.20\) from \(170,500,1000,3000\), respectively (also .20 at 30000 and 1000000). The scaled \(W\) and unscaled \(W/L\) decrease on every stated ray by the positive-mixture derivative tests in d02_analysis.md. For polynomial results extend the middle floor to \(B=230\), then use \(D^{\rm df}_{b_0}\): largest scaled log-power 4 and slowest rate \(1/8\) make the entire tail decreasing, so check at 230. This proves the joins without the density premise for the polynomial conclusions. Both branches are checked at common endpoints. More generally, for any \(z\in[0,1-b]\) and onset \(a\ge10\), a parametric sufficient coefficient is the maximum of the scaled ceilings from the applicable pieces between \(a\) and a chosen split \(B\ge\max(a,100)\), and the scaled late ceiling at \(B\), provided the monomial derivative tests hold from \(B\). In each finite piece use the two marked endpoints for increasing versus decreasing terms. This is a whole-ray test, and different splits and admissible \(k,s_0\) can be compared without assuming a unique empirical switch.

The limiting **certificate** coefficient in the rate-\((1-b)\) scale is \(2w(b)+4\cdot10^{-12}\), in \((.01044,.01045)\) for B0 and \((.14630,.14631)\) for D02. The scaled continuous mixture away from the endpoint tends to 0 by dominated convergence; the remaining terms tend to 0 except for the boundary mass and the high-ordinate primitive. This is not a lower bound on any prime error or a constant optimality claim.

**Density-free and direct variants.** With \(D_{b_2}^{\rm df}\), (B), and \(\widehat V\), the common rate-\(5/32\) coefficient is \(.01421L^2\) from \(L=200\), verified by separating the scaled decreasing ratio after division by \(L^2\) and the decreasing exponentiation factor. Thus rate \(1/8\) coefficient .000037 from 600 and rate .14 coefficient .00125 from 1000 hold, by decrease of the respective \(L^2e^{-(5/32-z)L}\) and the endpoint tests. For pure raw use of D02 in local and absolute integral terms, write \(r=5/32\). Before prime powers the weighted error costs
\[
 e^{-rL}[L^2+(L^2+2L/r+2/r^2)/r]/64,
\]
and the log-product error costs \(e^{-rL}[L+(L+1)/r+1/r^2]/64\). Add \(\widehat V\) and \(\widehat V/L\), respectively, and exponentiate the product bound. The endpoint ratios and monotonicity from 200 give rate-\(5/32\) coefficients \(.120L^2\) for the first three and \(.123L^2\) for weighted. This weaker D02 branch still beats all old uniform pure powers on \(L\ge500\); at 200 even the raw local estimate is worse than the B0 local density bound. It neither proves below-200 improvements nor explains removal of the log factor.

## Exact finite joins

Use finite_d02.py (ordinary and --extended), and power_new.py. The sieve marks from \(p^2\) and enumerates exactly the primes. The inherited integer outward log and loglog blocks of weighted.py and smallprod.py enclose the running sums and log-products. The Euler-constant bracket is tightened to
\[
 H_n-\log n-\frac1{2n}+\left[\frac1{12(n+1)^2},\frac1{12(n-1)^2}\right],\quad n=10^5 .
\]
Indeed comparing \(1/t\) with quadratics of the endpoint second derivatives bounds each trapezoidal error on \([j,j+1]\) between \(1/[6(j+1)^3]\) and \(1/(6j^3)\); summing and comparing with the integrals from \(n+1,n-1\) gives the bracket. Normalizer primes go through \(N=66000000\) for the polynomial runs and \(N=5000000\) for power_new.py. For the \(B_3\) tail use the inherited main \(-\log(1-1/N)\) with error \(\eta[2/(N-1)-\log(1-1/N)]\), \(\eta=.2/\log^2N\) by Dusart Thm 4.2 (p.11, LF959–1010, .2 row beginning at 3594641). For the tail in \(M\), the square main \((2N\log N)^{-1}\int_0^\infty e^{-v}/(1+v/\log N)\,dv\) is bracketed by degrees 9 and 8 of the geometric expansion after integration. The theta error bound is \(\eta[(N\log N)^{-1}+\text{main upper}]\) by partial summation, and higher powers cost \(1/[6N(N-1)]\) by summing the integer majorant, as in smallprod.py. Prime and normalization truncation errors are directed, including at \(N\).

For every prime-free \([p,q)\), check with the post-\(p\) prefix and clip the left endpoint to the query onset. Conservatively include the pre-\(q\) limit unless \(q\) equals the onset; the next cell always uses the post-jump prefix. The final composite endpoint is included. On each active cell \(|D_Q|<.1\) is checked at the endpoints. The scaled signed product derivatives are \(L^2(2e^{D_Q}-3)<0\) for \(Q\) and \(L^2(4e^{-D_Q}-3)>0\) for \(P\). The scaled signed sum derivatives are \(L^2(3E_1-1)\) and \(L(2E_{\log}-L)\), negative by the verified bounds \(E_1<1/3,\ E_{\log}<1\) and \(L>2\). Thus each sign uses its corresponding endpoint. Convert log magnitudes using \(1-e^{-d}\le d\) and \(e^d-1\le d+d^2/[2(1-d)]\) for \(0\le d<1\), from the exponential series. This tightens the old \(d/(1-d)\) upper conversion. Exhaustive finite coverage and the analytic tails prove the stated real rays.

In the power run bound unscaled errors at the clipped endpoints and multiply by the conservative upper scale of the whole cell (the integer slabs from power_bridge.py). Endpoint 24154954 is composite and above \(e^{17}\). Every early D02 bridge coefficient through the \(15000000\) row exceeds the analytic coefficient from 17. For .002275 from 40000000 and .001537 from 150000000, use the polynomial ceilings through \(e^{18}\) and \(e^{19.03}\); \(e^{L/8}/L^2\) increases for \(L>16\), so scale with the corresponding right endpoint before joining the power tail. run_d02.py checks all numerical obligations for the receipts. The receipts are reproducible from their linked generators; the assertions checking maxima are not substitutes for the cell proofs.

## Whole-domain pointwise envelope and improved alternative transforms

1. Start with all applicable signed local intervals from mertens.md and spectral_repair.md, and the original estimates there (including CH2 for any permitted \(T\), Dusart applicable rows, and FKS's literal bounds). Intersect with (A) at every stated \(s_0,k\), the density-free interval, and D02's raw interval only when allowed at \(L\ge200\). Include a \(\theta\) interval by subtraction of \(q=e^{-L}(\psi-\theta)(e^L)\) and by the exact Möbius identity \(\theta(x)=\sum_{j\le\log x/\log2}\mu(j)\psi(x^{1/j})\), from finite inversion of \(\psi(x)=\sum_j\theta(x^{1/j})\). Keep the inherited Dusart and finite-RH \(\theta\) intervals. This incorporates the new cap at smaller arguments only where the corresponding branch is valid.
2. For the \(\psi\) transforms intersect (B) with absolute or signed endpoint-integrated bounds. For \(\theta\), shift (B) by subtracting the full permitted interval for \(\int_L^\infty qk\) and compete with the direct \(\theta\) integration, with **no** \(U,T_0,V\) terms in \(\theta\)-only formulas. For \(A\) use \(u-\int u\) with the new bounds, intersected with the quoted CH2 weighted intervals; also use \(D_Q-U=A(L)/L-\int_L^\infty A(t)t^{-2}\,dt\). These are explicit integrals of endpoint functions (not integrals of unknown prime values); the bounds converge since they can use a positive decay rate. Interval intersections need no probabilistic independence.
3. Keep the old prime-power intervals, and \(V_+\) on \(10\le L\le58\), and further intersect with the following computable signed refinement. For \(m\ge2,\ y>1,\ f(v)=v^{-m}\) or \(v^{-m}/(m\log v)\),
\[
 \int_{(y,\infty)} f\,d\theta=\int_y^\infty f(v)\,dv
 -f(y)(\theta(y)-y)+\int_y^\infty[-f'(v)](\theta(v)-v)\,dv.
\]
Use the improved signed \(\theta\) interval in each term, and nonnegativity. Sum through any \(m\le k\), with \(y=e^{L/m}\) for \(V,U+T_0\) or \(y=x\) for \(T_0\). The omitted log-weighted tail is at most
\[
 1.000058[2+\tfrac{k+1}{k}\min(2,(1-e^{-L/(k+1)})^{-1})]e^{-kL/(k+1)}
\]
by the same geometric split at \(e^{L/(k+1)}\); independently it is at most \(2[\log2/2^{k+1}+\int_2^\infty(\log v)v^{-k-1}dv]\) by comparison with all integers. The latter tends to zero with \(k\). For unweighted tails use either ceiling divided by \(L\), since \(m\log p>L\). Intersect \(U=(U+T_0)-T_0\) with \(U\ge0\). No tail contains a power equal to \(x\).
4. Convert \(D_Q\in[l,h]\) to the separate product envelopes \(\max(e^{-l}-1,1-e^{-h})\) and \(\max(e^h-1,1-e^l)\); for a signed sum interval use the greater of its upper endpoint and minus its lower endpoint. Take the minimum with every applicable established table, literal original branch and finite-sieve bound. The refined finite normalizers and exact arithmetic prefixes can also be used at a given \(x\) without taking the whole finite-run maximum. For \(1<x<2\) use exact empty sums and products. This is a valid whole-domain prescription, never enlarging the inherited envelope at any point. It does not require claiming that every switch point is known.

## Comparison at the level of hypotheses; remaining limits

This is a within-method reconstruction and improvement of the B0 envelope, retaining all original results and the D01 floor, not an independent blind run. Matching the new rate from **any one** of the four errors over B0 would itself establish the stronger zeta exclusion. In detail, any eventual \(O(e^{-rL}L^j)\) on one of them, for \(1/8\le r\le5/32\), implies the cap \(1-r\). For products take logarithms on a ray where the errors are small. The prime-power tails above are \(O(e^{-L/2})\) or better. Subtracting them gives the assumed rate for \(A\) in the weighted case or for \(F=A/L-\int_L^\infty A(t)t^{-2}dt\) in the other cases. The latter identity inverts as \(A(L)=LF(L)+\int_L^\infty F(t)dt\), by absolute integration and interchange (the old cap ensures convergence). Finally \(B_1'=-A-B_1\) a.e.; from finite \(a\), solve
\(B_1(L)=e^{a-L}B_1(a)-\int_a^L e^{t-L}A(t)dt\).
The convolution retains the power since \(r<1\), taking a nonnegative integer log exponent as an upper bound if necessary. Thus \(u=A+B_1\) has the claimed power with at most additional logarithms, and the Euler-product Mellin argument excludes zeros to the right. This does not assert unproved independence of premise closures or global best-known status.

The early polynomial bottleneck is the arithmetic prefix and finite information, not D02. Separating squares and cubes, sharpening the signed primitive, normalizing more accurately, and extending the finite join helped over B0. At late \(L\) the positive boundary weight in the density envelope controls the constant; the primitive alone cannot reduce it, and using absolute integration leaves a log-square loss. The pure power relies on Cor.2.9 as stated; density-free and raw variants are retained. Failure of a sufficient test is not a counterexample unless separately proved.
