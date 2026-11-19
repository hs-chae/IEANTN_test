# Mertens products and prime sums (B0; hence also B0+D01)

Put \(L=\log x\), \(P=\prod_{p\le x}(1-1/p)\), \(Q=1/P\), and use the four nonnegative errors in this order:
\[
 \begin{split}
 E_1&=\left|\sum_{p\le x}1/p-\log L-M\right|,\qquad
 E_P=|e^{\gamma_E}LP-1|,\qquad E_Q=|e^{-\gamma_E}Q/L-1|,\\
 E_w&=\left|\sum_{p\le x}(\log p)/p-L+B_3\right|.
 \end{split}
\]
The constants are exactly
\(M=\gamma_E+\sum_p(\log(1-1/p)+1/p)\) and
\(B_3=\gamma_E+\sum_p\log p/[p(p-1)]\), as in Dusart 2018 Theorems 5.6 and 5.7 (PDF pp. 17–19). All upper bounds below are non-strict unless indicated. Domains are real, with included endpoints.

## Explicit portfolio and comparison

* Retain original \(.2/L^3\) for \(E_1\) on \(x\ge2278383\) and \(E_P,E_Q\) on \(x\ge2278382\) (Dusart Theorems 5.6, 5.9, pp. 17–20). Retain \(.3/L^2\) for \(E_w\) on \(x\ge912560\) (Theorem 5.7). The products’ common derivation is correlated, not two independent experiments.
* **Finite block pointwise envelope starting at 1000.** Every “blocks” row of finite_final.txt gives four upper constants in units \(10^{-4}\) for \(L^3E_1,L^3E_P,L^3E_Q,L^2E_w\) on the displayed closed interval. Take minima at shared endpoints and with any other applicable branch. These include earlier onsets at relaxed constants, e.g. on \(x\ge1000\) one can use the whole-ray constants \(2.2466,2.2298,2.2432,2.5513\) in the displayed normalized errors (multiply by the appropriate inverse log power). At \(x\ge10^6\) the weighted constant becomes .296; at \(x\ge2278383\) the product constants are both .1999; at \(x\ge4\cdot10^7\) the three cubic constants are .0702 and the quadratic constant .0749.
* **Onsets at fixed constants.** For each finite_final.txt “margin” row with column index 0,1,2,3, use the displayed margin multiplied by \(10^{-4}\) from one plus the displayed “last” endpoint through \(x=500000000\). Extend it to the entire ray if the margin is at least .0667 for columns 0–2 or .0726 for column 3. For example .199 for the first three from \(2278422\), .12 from \(8789190\), .08 from \(30971684\) there and from \(33930192\) in the weighted sum. Constant .0667 is valid for the first three from \(40886832\); .0726 for the weighted sum from \(40884830\). These are sufficient onsets and not claims of the last actual failure. Close to the original cutoffs, use the exact fixed-constant refinements described next. If the “last” value is zero, restrict the finite result to \(x\ge1000\).
* **Sharp real onsets at the original constants.** For the \(E_1,E_P,E_Q,E_w\) original constants \((.2,.2,.2,.3)\), with the same powers \((3,3,3,2)\), there are unique last crossings \(\zeta_i\) as follows. Here “offset bracket” bounds \(\zeta_i-n\) strictly, and at the crossing \(L^k E_i\) equals the original constant.
   
   | error | \(n\) | offset bracket |
   |:---|---:|:---|
   | \(E_1\) | 2278382 | (.11,.12) |
   | \(E_P\) | 2278381 | (.57,.59) |
   | \(E_Q\) | 2278381 | (.70,.72) |
   | \(E_w\) | 912559 | (.9972,.9975) |
   
   Each original error bound holds on the closed real ray \([\zeta_i,\infty)\), and fails on \([n,\zeta_i)\). Thus the original integer onsets are sharp at those exact constants but not the real onsets. Using the upper bracket endpoints gives explicit rational sufficient onsets. If the same onset is wanted for both products, use the later crossing (for Q). The original-point estimates and all later x also follow from the monotone finite certificate and analytic join, separately from the original large finite Mertens computations.
* **Analytic bridge and arbitrary log powers.** For \(L\ge20\),
\[
 (E_1,E_P,E_Q)\le(.0667/L^3,.0667/L^3,.0667/L^3),\qquad E_w\le .0726/L^2.
\]
Thus there is no gap at the finite/analytic join (since \(e^{20}<500000000\)). The signed, pointwise envelopes below are often much smaller, and apply on the analytic domain together with the constant and exponential ones.
* **Sharper exponential tails.** For each row and all \(L\ge J\), use
\[
 E_1,E_P,E_Q\le c\,e^{-L/8}/L,\qquad E_w\le c\,e^{-L/8}.
\]
  | \(J\) | \(c\) |
  |---:|---:|
  |150|.036|
  |182|.02164|
  |190|.02046|
  |194|.020|
  |195|.019865|
  |200|.019354|
  |250|.016438|
  |400|.013604|
  |810|.011885|
  |1500|.011247|
  |3000|.010904|
  
  A continuously varying coefficient is below. The extra \(1/L\) is genuine for the first three. The new oscillatory transfer avoids multiplying the main ψ constant by 9. Alternatively at any such onset \(J\), these imply log-power bounds \(E_1,E_P,E_Q\le c e^{-J/8}J^{k-1}/L^k\) for \(J\ge8(k-1)\), and \(E_w\le c e^{-J/8}J^k/L^k\) for \(J\ge8k\), by monotonicity. Compared at the same onset \(L=200\), the exponential branch strictly improves the published log-power constants everywhere to its right: \(L^2e^{-L/8}\) decreases there and the strict comparison holds at 200. For other shapes use the pointwise minimum, not an inferred crossover from a grid.

**Premise and source comparison.** The above retain Dusart's strongest direct bounds where applicable and sharpen by new B0 deductions. In the complete envelope comparison, exact D01 adds no improvement, by the B0 implication (common.md). More concretely, directly inserting D01 into the signed ψ transfer below yields symmetric main bounds \(e^{-L/8}(9L+72)/64\) for the reciprocal sum and log-products, and \(e^{-L/8}(9L^2+128L+1024)/64\) for the weighted sum, plus the stated power corrections. Simply replacing \(1/64\) by B0's .0045 gives smaller bounds on that entire ray, without even using density or the new oscillatory mechanism. Retaining original FKS/PT estimate shapes and other pointwise ψ/θ branches is compatible with the minima below; no global minimum over all possible B0 proofs is claimed.

## Exact tail identities and signed envelope

Define \(J_1=\sum_{p\le x}1/p-\log L-M\), \(J_w=\sum_{p\le x}\log p/p-L+B_3\), and \(\Delta=\log Q-\gamma_E-\log L\). Write \(k(u)=(u+1)/u^2,\ \eta(u)=e^{-u}\theta(e^u)-1,\ v(u)=e^{-u}\psi(e^u)-1\). Dusart's partial summation formulae in the proofs of 5.6, 5.7 give
\[
 J_1=\eta(L)/L-\int_L^\infty k(u)\eta(u)\,du,\quad
 J_w=\eta(L)-\int_L^\infty\eta(u)\,du,\quad
 \Delta=J_1-C(x),\quad C(x)=\sum_{p>x}\sum_{j\ge2}1/(j p^j).
\tag{5}
\]
Here \(0\le C(x)\le1/(2\lfloor x\rfloor)\le1/[2(x-1)]\), bounding by \(\sum_{n>\lfloor x\rfloor}1/[2n(n-1)]\). The \(\Delta\) identity is exact by the defining series for M.

For an entire-domain signed bound let \(\ell(u)\le\eta(u)\le h(u)\) be any applicable pointwise original θ envelope, including the new estimates from common.md. The lower and upper for \(J_w\) are \(\ell(L)-\int_L^\infty h\) and \(h(L)-\int_L^\infty\ell\); for \(J_1\) apply the same recipe with endpoint factor \(1/L\) and kernel \(k\). For \(\Delta\), lower the first endpoint by \(1/[2(x-1)]\), keep the upper. Use \(\eta\le0\) in the certified sign interval and \(\eta\le-.208e^{-u/2}\) for \(20\le u\le29.9\) (CH plus the lower power bound). At any u choose the maximum of usable lower bounds and minimum of upper bounds before integration. In particular take the signed CH, finite RH, DEN and G bounds from common.md and the rows of Dusart Thm. 4.2, PDF p. 11, with their original left endpoints. One can also include the PT Thm. 1 table / Cor. 1, PDF pp. 2–3, and FKS Thms. 1.1, 1.2 / Cor. 1.4, PDF p. 2 and their applicable tables; for a ψ bound subtract the interval for \(e^{-u}D(e^u)\). All integrals converge because the envelope includes G+P on the tail (the two sides can each be kept within it). Additional lawful pointwise estimates can only improve this interval recipe.

There is a second transfer in terms of ψ directly:
\[
 \begin{split}
 J_w&=v(L)-\int_L^\infty v(u)\,du+B_{\rm pow}(x),\\
 J_1&=v(L)/L-\int_L^\infty k(u)v(u)\,du+A_{\rm pow}(x),\\
 \Delta&=v(L)/L-\int_L^\infty k(u)v(u)\,du+A_{\rm pow}(x)-C(x),
 \end{split}
\tag{6}
\]
where \(B_{\rm pow}=\sum_{p^j>x,\ j\ge2}(\log p)/p^j\), \(A_{\rm pow}=\sum_{p^j>x,\ j\ge2}1/(jp^j)\). This is (5) using \(\eta=v-e^{-u}D(e^u)\) and partial summation; the tail starts strictly above x including at a prime power. In particular \(B_{\rm pow}=-D(x)/x+\int_x^\infty D(t)/t^2dt\), so for \(x\ge121\)
\[
 0\le B_{\rm pow}\le b_{\rm pow}(L)=1.000102e^{-L/2}+2.67e^{-2L/3},
 \qquad
 0\le A_{\rm pow}-C\le A_{\rm pow}\le b_{\rm pow}(L)/L.
\tag{7}
\]
The coefficient 1.000102 uses \(2(1.000001)-.9999\), not a twice-counted main term. A lower bound for \(B_{\rm pow}\) is \(\max(0,.999799e^{-L/2}-1.78e^{-2L/3})\). To improve (6), replace the symmetric pointwise transfer for ψ by signed integration where available, and intersect the interval for \(W=v(L)-\int_L^\infty v\) with CH2's direct bound \([-a-113.67e^{-L/2},a+113.67e^{-L/2}]\). Indeed \(W=J_w-B_{\rm pow}=\sum_{n\le x}\Lambda(n)/n-L+\gamma_E\) by the exact \(B_3\) definition. Also
\(v(L)/L-\int_L^\infty k v=W(L)/L-\int_L^\infty W(u)/u^2\,du\),
by inserting the definition of W and interchanging absolutely convergent integrals. These are alternative valid branches, not independent evidence.

For an interval \(\Delta\in[d_-,d_+]\), use the exact relative-product bounds
\(\max(1-e^{-d_+},e^{-d_-}-1)\) for \(E_P\), and \(\max(e^{d_+}-1,1-e^{d_-})\) for \(E_Q\). Intersect the available Δ intervals before exponentiating. For signed \(J_1,J_w\) take the maximum of the endpoint magnitudes. Take pointwise minima with the certified blocks, last-endpoint margins, original direct bounds, and analytic tails. This specifies an entire-domain envelope for each of the four errors, without treating the two reciprocals as independent.


For example the CH direct W branch gives \(E_w\le1.049\cdot10^{-12}\) and \(E_1,E_P,E_Q\le(2.097\cdot10^{-12})/L\) on \(L\ge80\). In the latter three the coefficient for the absolute log/additive bound is at most
\(2a+113.67 e^{-L/2}(1+2/L)+b_{\rm pow}(L)\) by the W-integral formula; all terms decrease, and the product conversion uses \(s/(1-s)\). The weighted bound is \(a+113.67e^{-L/2}+b_{\rm pow}\). The rational tests at 80 and comparison with the exponential branch at and after 200 prove all-ray comparisons thereafter.

## Oscillatory transfer: proof of the small tail constants

Fix \(L\ge150\); on the whole interval \([L,2L]\) take \(T=e^{2L/5}\) in FKS 3.2. It exceeds \(2L,51\) and satisfies \(5T+2<e^{L/2}\). At each \(u\) the theorem may choose a different \(T^*(u)\); do **not** integrate a sum with that varying cutoff as if it were fixed. Instead replace it by the fixed sum
\(Z_T(u)=-\sum_{|\gamma|\le T}e^{(\rho-1)u}/\rho\), bounding separately the strip \(T<|\gamma|\le2.45T\). For \(\beta\le.80\) the strip contributes at most \(.14 L e^{-u/5}\). Indeed apply FKS Lemma 2.1 to \(U=T,\ V=2.5T\), with the Rosser constants \(b_1=.137,b_2=.443,b_3=1.588\) in Remark 2.2. In (2.1), \(R(T)\le\log T\), the first bracket is \(<.17\), \(\log(V/U)<1\), and \(\log(\sqrt{VU}/(2\pi))\le2L/5\); \(2B_1(T,V)\le .34(2L/5)+4\log T/T<.14L\). For \(\beta>.80\), divide \(2N(.80,2.45T)\) by T and use QRH. With \(m=2L/5+1\) this is bounded by \(S_T e^{-u/8}\), where
\[
 S_T=40m^4 e^{-14L/75}+8m^2e^{-2L/5}.
\]
Here \(2(8.162)(2.45)^{8/15}<40,\ 2(3.693)<8,\ \log(2.45T)<m\), and \(m^{3.4}\le m^4\). The remaining Perron error at u is \(2.091u/T\).

For \(w=1\) or \(w(u)=k(u)\), integration by parts against the exponent gives
\[
 \left|\int_L^{2L}w(u)e^{(\rho-1)u}\,du\right|
 \le 2w(L)e^{(\beta-1)L}/|\rho-1|.
\]
Indeed \(w\) is positive and nonincreasing, and the sum of the two endpoint weights and the integral of \(|w'|\) is \(2w(L)\). Write \(K_t\) for K with the two-slope improvement of common.md. Above H the integration denominator is at least H. The absolute endpoint sum itself is bounded by \(e^{-L/8}[K_t(L)+.008L^2e^{-3L/40}]\) by the zero estimates in common.md (not merely an absolute bound on v): with the larger \(T\), increase the low-zero coefficient .018 to .026 using \((2L/5)^2/(2\pi)+1.8642\le .026L^2\). At \(|\gamma|\le H\), \(\beta=1/2,\ |\rho-1|\ge1/2\), giving the factor \(.104L^2e^{-L/2}\) after including the preceding 2. The integrals of the strip and Perron terms are at most \(w(L)(.7L e^{-L/5}+8S_Te^{-L/8})\) and \(w(L)3.1365L^2e^{-2L/5}\). Beyond \(2L\) the absolute integral is \(\le w(L)8K_t(2L)e^{-L/4}\). Consequently
\[
 \left|\int_L^\infty w(u)v(u)\,du\right|\le w(L)e^{-L/8}I(L),
\]
where
\[
 I(L)=2[K_t(L)+.008L^2 e^{-3L/40}]/H+.104L^2e^{-3L/8}+.7L e^{-3L/40}
            +8S_T+3.1365L^2e^{-11L/40}+8K_t(2L)e^{-L/8}.
\tag{8}
\]
This removes the large integral loss of a purely unsigned transfer. It gives new signed intervals in (6): for instance \(\Delta,J_1\) both lie between \(-d_0\) and \(d_0+b_{\rm pow}/L\) for \(d_0=e^{-L/8}[K_t+(1+1/L)I]/L\).

For simplified constants define \(C_w=K_t+I+e^{L/8}b_{\rm pow}\), \(C_d=C_w+I/L\). Upper envelopes are \(e^{-L/8}C_w\) for \(E_w\), \(e^{-L/8}C_d/L\) for \(E_1\), and the latter with \(C_d\) replaced by \(C_d/(1-C_d e^{-L/8}/L)\) for the products (use \(e^s-1\le s/(1-s)\) for \(0\le s<1\)). All three coefficients decrease on \(L\ge150\), by decreasing individual exponents times powers, the monotonicity of \(K_t\), and the rational factors. For example each power times an exponential in \(S_T\) decreases already at 150. mertens_cert.py checks at each J, with rational enclosures. There is also a weaker absolute-transfer branch using \(K(L)\) alone, \(C_w=9K\) and \(C_d=(9+8/L)K\) with the extra \(C(x)\) error for products; the oscillatory improvements follow from the fixed-cutoff derivation, not from manipulating its coefficient. The limiting coefficient of the new upper envelope is \(.01058(1+2/H)\), with the small \(2/H\) term from our use of a uniform bound for the integration denominator. No optimal asymptotic constant is asserted.

## Analytic bridge with exact interval checks

For \(20\le u<29.9\) use \(b(u)=1.752e^{-u/2}+1.78e^{-2u/3}\) as the magnitude bound on η, from the stronger CH Lemma 9.2 and Dusart Cor. 4.5; here \(\eta\le-.208e^{-u/2}\). On \([29.9,58]\) use \(b(u)=u^2e^{-u/2}/25\) from finite RH, and on \([58,200]\) the CH+P bound. On \(u\ge200\), use \(K(u)e^{-u/8}\), with \(K(200)<.022\). Every branch covers its joins, and \(\eta\le0\) through \(s=39.47\). For the upper signed bound in (5), use the full integral of \(b\), plus an endpoint term only if \(L>s\); if \(L\le29.9\), subtract the available positive lower bound on \(-\eta(L)\) (and divide it by L for \(J_1\)). For the lower signed bound, subtract the full endpoint magnitude and integrate \(b\) only from \(\max(s,L)\). For \(J_1\), use \(k\) as the weight.

In precise() in mertens_cert.py, partition the four intervals using closed cells \([l,h]\) of width at most .1; both adjacent formulae are valid at a join. Upper bounds for the unweighted integrals on every cell use exact primitives for sums of exponentials or \(u^2e^{-u/2}\); for the weighted integral use \(k(l)\) times the unweighted cell bound. Add a common analytic tail \(8K(200)e^{-25}\), with factor \(k(200)\) if weighted. Compute backwards and hence bound the suffix integral for **every** \(L\in[l,h]\). Endpoint magnitudes use l; the positive subtractive terms use h. \(L^2,L^3\) are bounded above by \(h^2,h^3\). The products use the two signed endpoints separately (for \(a\ge0\), \(1-e^{-a}\le a,\ e^a-1\le a/(1-a)\) when \(a<1\)). The resulting ceilings in units \(10^{-6}\) are \(66693,66693,66694,72550\). The analytic tail beyond 200 is already below the required inverse-log constants, from the exponential row there and monotonicity. This proves the bridge and the joins in the finite portfolio.

## Finite arithmetic algorithm and proof

finite.cpp, compiled with assertions enabled, uses only fixed-point integer interval arithmetic and a complete sieve through \(N=500000000\). Marking multiples from \(p^2\) for each surviving \(p\le\sqrt N\) is exact: each composite has a least prime factor at most \(\sqrt N\), and no primes are marked. The code sums three quantities at each prime: \(1/p,\log p/p,\log(1-1/p)^{-1}\). On a gap \([p,q)\) the prime quantities are constant. The signed scaled discrepancies \(L^3J_1,L^3(e^{-\Delta}-1),L^3(e^\Delta-1),L^2J_w\) are monotone: their L derivatives are
\(L^2(3J_1-1),L^2(4e^{-\Delta}-3),L^2(2e^\Delta-3),L(2J_w-L)\), respectively. On the clipped gaps the raw discrepancies are monotone and the endpoint arithmetic checks they lie in \([-1/8,1/8]\), with \(L\ge\log1000>6\); hence the signs of these derivatives are fixed. It suffices to bound both scaled endpoints (the left limit at q is allowed). Both sides of a prime jump are covered by consecutive intervals. Clipping an interval at block boundaries preserves this property; an extra closed endpoint check never weakens the conclusion. A failing subinterval in “last” ends no later than the displayed integer; hence every real x from the next integer through N is covered. It is a sufficient, not necessary, threshold.

With scale \(S=2^{61}\), each ball stores an inclusive pair of integers divided by S. lograt reduces a positive ratio ≥1 to [1,2), then extracts one of \(1+i/256\) and uses the residual atanh series. series uses \(r\le1/3\), rounds each multiplication and division outwards, and adds up to \(4r^{2n+1}\) for the omitted tail to the \(2\operatorname{atanh}(r)\) approximation. That covers the geometric tail because \(2/(1-r^2)<4\). The \(\log\log\) enclosure is monotone on the log balls, and \(-\log(1-1/p)\) is the same series with ratio \(1/(2p-1)\). Gamma uses \(H_n-\log n-1/(2n)\) at \(n=10^6\) as lower bound and adds \(1/n^2\) to the upper. In fact the successive differences of the corrected harmonic approximation are the positive trapezoid errors for \(1/t\) on \([n,n+1]\), bounded by \(\sup|(1/t)''|/12\le1/(6n^3)\) (integrate the error kernel or twice integrate by parts). The sum of these differences is less than \(1/n^2\) and the approximations tend to Euler's constant.

The M and \(B_3\) tails after N are enclosed more tightly than by comparison to all integers. By Dusart Thm. 4.2 (\(k=3,\eta_3=1,\ x_3=89967803\)), for \(t\ge N\), \(|\theta(t)-t|\le\delta t,\ \delta=1/8000\) since \(\log N>20\). For the \(B_3\) tail, the sum of \(\log p/p^2\) differs from \(1/N\) by at most \(3\delta/N\) by partial summation (one endpoint and two integral units). The replacement \(p^2\mapsto p(p-1)\) multiplies each by at most \(1+1/(N-1)\). This gives the exact stored interval \([.999625/N,1.000376/N]\). For the M tail (negative of \(C(N)\)), the sum of \(1/p^2\) is within \(3\delta/(N\log N)\) of \(I_N=\int_N^\infty dt/(t^2\log t)\). The latter is between \(1/[N(\log N+1)]\) and \(1/(N\log N)\); the lower follows by integrating the tangent at the mean 1 with weight \(e^{-v}dv\) after \(t=Ne^v\). Since \(20<\log N<20.1\), and \(C(N)\) is between half this prime-square sum and the same quantity times \(1+1/(N-1)\), the code's \([1/(44N),1/(39N)]\) contains it.

Integer operations fit: sieve indices stay below \(N+\sqrt N<2^{31}\). Directed products of scaled series powers and ratios are at most \(S^2\) before division. In lograt when used on a log ball, the reduced denominator is at most \(16S\) and the residual numerator is smaller than that denominator; multiplying this numerator by S stays below \(2^{126}\). Ordinary log arguments are ≤N. Other ratio and table intermediate integers fit readily below this bound. In scaled(), after at most three powers the overall magnitude is at most \(21^3 S\), and the split multiply uses a remainder \(<S\) times a log \(<21S\), safely below \(2^{127}\). expm() multiplies quantities \(<S\) by S. Summing all directed increments is bounded by the all-integer harmonic series (for log weight also multiply by \(\log N<21\)) plus \(O(N)\) rounding units; the resulting integers, including constant intervals, fit in signed 128 bits. Final reported gamma, M, \(B_3\) endpoints are individually below \(2^{63}\). This is a finite algorithm proof and executable replay, not a formal correctness proof of the C++ compiler.

## Proof of the sharp real cutoff refinements

The “probe” records are exact balls at specified integers with right-continuous counts, in order \(L/8,J_1,\Delta,J_w\), each pair in units \(1/S\). Within the unit intervals in the cutoff table, the prime sums and products have no jumps, even at the right endpoint (912560 and 2278382 are even, 2278383 is divisible by 3). Therefore move the probe at n to any rational \(x\in[n,n+1]\) by subtracting \(\log\log x-\log\log n\) from \(J_1,\Delta\), or \(\log x-\log n\) from \(J_w\). cutoffs.py computes rational enclosing logarithms and tests both strict signs at all bracket endpoints, as well as at the two integers. All three signed quantities used in these comparisons are positive and small throughout their respective unit intervals by the endpoint checks and unscaled monotonicity. At the scaled level \(L^3 J_1,L^3(1-e^{-\Delta}),L^3(e^\Delta-1),L^2J_w\) strictly decrease there, by the derivatives just proved. Thus each crossing is unique, with equality included; the block table starts the four required rays at \(n+1\) and the analytic join extends them. The sign checks for the relative products use both sides of exp, not only an upper bound on the log-product. This proves the real and integer sharpness statements at these fixed margins.

## Attempts, limitations

The smaller sieve to 66 million did not certify the aggressive coefficient trials. The unsigned CH transfer also yielded a weak join; extending the exact sieve, enclosing both finite constant tails, using the signed θ interval and accumulating weighted integrals with a partition gave the smaller joined constants. For large L a first density transfer gave an explicit .199 exponential constant for the cubic branches from 200 (see mertens_result.txt), but much of this came from the triangle inequality in the tail. Controlling the truncation strip and oscillation improved it to .019354 there, and .020 already from log 194, without changing B0. The best eventual coefficient of the present argument is now set mainly by the prime-side ψ endpoint density estimate, not by integration, product exponentiation, or D01. At the original tight constants we verified actual local violations just before each crossing and sharpened the real onsets. At other margins the “last” outputs do not prove optimality or a counterexample. Further improvements could come from a sharper bound on the weighted density near the QRH boundary, tighter small-x certificates at precise crossover points, or direct cancellation of the ψ endpoint term; none is required for the claimed joins.

