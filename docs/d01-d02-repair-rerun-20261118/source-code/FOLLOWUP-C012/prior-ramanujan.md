# Ramanujan gap: connected sign, margins, higher-order profiles

Let \(L=\log x\). With B0, the exact connected real sign conclusion is \(R(x)>0\) for all \(x>\xi\), where
\[
 38358837682.21792636<\xi<38358837682.21792637.
\]
Here \(R(\xi)=0\), and \(\xi\) is the largest real counterexample to strict positivity. The integer sign conclusion begins at \(38358837683\). The connected sign theorem is input-independent (it carries to B1 unchanged); the stronger high-order margins below do use the extra input.

**Correction to the published real endpoint.** Let \(n_0=38358837682\). Platt–Trudgian 1809 PDF p. 3 Theorem 2 prints the range \(n_0<x\le e^{58}\). Read literally for every real number with inclusive \(\pi\), it is false, for example at \(x=38358837682.1\). We retain only its integer restriction and use monotonicity of \(R\) on every half-open interval \([n,n+1)\) with \(n>e\) (constant \(\pi(x)\), nondecreasing \(\pi(x/e)\), increasing \(x/\log x\)). This covers \([n_0+1,e^{58}]\) using the inherited finite statement for integers, and the new quantitative proof covers \([e^{58},\infty)\). This fills the gap to the published analytic onset \(e^{3915}\). Dudek–Platt 1407 PDF p. 2 Theorem 1.2 (\(x\ge e^{9658}\)) is subsumed. Their Theorem 1.3 assumes full RH and explicitly says *integer*. The real stepping argument in their Lemma 3.3 writes a bound by \(\varepsilon\) for the number of intervening primes; for general real endpoints the elementary available bound is \(\lceil\varepsilon\rceil\). We do not treat that as an independently corrected/reverified finite computation. If the inherited integer claim is removed, the short new endpoint computation and the analytic ray do not by themselves prove the intervening finite range.

At \(n_0\) and \(n_0+1\) the counts are both \(1644673232\), and throughout their intervening unit interval \(\lfloor x/e\rfloor=14111427770\) with count \(632207037\). Thus \(\xi\) is exactly the unique root of \(632207037 e x/\log x=1644673232^2\) there. The gap is negative at the left endpoint, positive at the right, and strictly increasing on the unit interval. endpoint.py and primecount.cpp certify the counts, signs and bracket; the displayed expression also gives the exact local quantitative profile. The prime count code starts with \(g(w)=w-1\) on all distinct positive quotients \(\lfloor n/i\rfloor\). Before the step at prime \(p\), it counts the primes below \(p\) together with integers \(\ge2\) with no prime factor below \(p\). It subtracts \(g(\lfloor w/p\rfloor)-g(p-1)\) for \(w\ge p^2\), exactly the composites with least factor \(p\). The test \(g(p)>g(p-1)\) detects primes; quotient closure and descending \(w\) ensure use of unmodified subcounts. After processing through \(\sqrt n\), all composites are removed. This is independent of the published finite computation, but only for the three named integer arguments.

## Explicit pointwise lower function

Set \(N=12,\ f(u)=\sum_{j=0}^{N-1}j!/u^{j+1},\ h(u)=2N!/u^N\). Using PV \(\mathrm{li}\), for \(u\ge30\),
\[
 e^u f(u)< \mathrm{li}(e^u)<e^u(f(u)+h(u)/u).
\]
The difference has derivative \(N!e^u/u^{N+1}\) with respect to \(u\); the proposed upper remainder has derivative at least this for \(u\ge30\). Check strict initial inequalities in verify.py by the convergent series \(\mathrm{li}(e^u)=\gamma+\log u+\sum_{j\ge1}u^j/(j\,j!)\). Its integration constant is \(\lim_{a\downarrow0}(-\int_a^\infty e^{-t}dt/t-\log a)=\gamma\). This follows by writing \(H_n=\int_0^n(1-(1-t/n)^n)dt/t\), subtracting \(\log n\), and taking dominated limits on \([0,1]\) and \([1,\infty)\). The gamma enclosure \(H_n-\log n-1/(2n)\le\gamma\le H_n-\log n-1/(2n)+1/n^2\) follows by the trapezoid rule for \(1/t\) on each \([j,j+1]\) (error \(\le\sup |f''|/12\) by integrating the linear interpolation error).

Use the following bound \(E_b(u)\) on \(ue^{-u}|\pi(e^u)-\mathrm{li}(e^u)|\) for \(u\ge35.984\). For \(u\le58\), use \(u^2e^{-u/2}/25.1327412\) from finite RH. For \(u>58\), choose the minimum of the following transports of \(\psi\) bounds \(B(u)=\sum c u^d e^{-au}\): \(C(u)=1.047198\cdot10^{-12}+113.67e^{-u/2}\), \(G_{7/8}\), and (only B1) \(G_{27/32}\). Add \(1.000000147e^{-u/2}+1.78e^{-2u/3}\) to each \(B(u)\) to obtain \(B_*(u)\). The bound is
\[
 E[B](u)=(2\cdot58/25.1327412)u e^{29-u}+
 \sum_{(c,d,a)\ {\rm in}\ B_*}c u^d e^{-au}
           \left(1+\frac1{u(1-a-2/58)}\right).
\]
Indeed, with \(z(v)=e^{-v}\theta(e^v)-1\), partial summation starting at 58 expresses the normalized \(\pi-\mathrm{li}\) as
\[
 z(u)+ue^{58-u}
   [e^{-58}(\pi(e^{58})-\mathrm{li}(e^{58}))-z(58)/58]
   +u\int_{58}^{u}e^{v-u}z(v)/v^2\,dv .
\]
The finite RH estimates for both anchor terms give \(2\cdot58/25.1327412\), and \(e^v c v^{d-2}e^{-av}\) has log derivative \(\ge1-a-2/58>0\), giving the integral bound.

For \(L\ge36.984\), let \(w=h+E_b\), except use \(w=h\) through \(L=43.74\) by the finite upper sign \(\pi<\mathrm{li}\). Put
\[
 {\cal E}(L)=L^4\{[L/(L-1)]E_b(L-1)+2Lf(L)w+w^2\}.
\]
Then
\[
 \frac{L^6 R(x)}{x^2}>{\cal P}(L)-{\cal E}(L),\qquad
 {\cal P}(L)=L^6[f(L-1)/L-f(L)^2].
\]
The lower bound for \(\pi(x/e)\) uses \(f(L-1)\); the upper for \(\pi(x)\) uses \(f(L)+w/L>0\), so squaring introduces no sign error. The neglected lower \(\mathrm{li}\) remainder is strictly positive. This rational-algebraic main term with explicit exponential error is an output, not the constant 1 alone. It also permits using exact finite-source constants and endpoints, retaining source sign wherever stronger, and signed transports of source intersections using the same identity. In a signed transport use the corresponding upper/lower endpoints in the integral and anchor from any eligible fixed point. Use the offset if directly comparing differently normalized \(\mathrm{li}\).

### Earlier finite quantitative island (B0)

The older finite sign result does not give a uniform quantitative margin. For \(28\le L\le29.9\) we get \(R(x)>.015\,x^2/L^6\), improved to \(.53\,x^2/L^6\) for \(29\le L\le29.9\). This uses the CH2 Lemma 9.2 *lower* bound \(\delta(v)\ge-.751e^{-v/2}\) and the Dusart power correction. Apply the signed anchor identity at 16, keep the upper sign \(\pi(x)<\mathrm{li}(x)\), and in the lower \(\pi\) error drop the nonnegative \(-z(16)/16\) inside the anchor. The lower error is thus bounded by the transport of \(1.751000147 e^{-v/2}+1.78e^{-2v/3}\), with anchor contribution \((16/25.1327412)u e^{8-u}\) and the factor \(1+1/[u(1-a-2/16)]\) for each term. All used finite source arguments are inside their domains: \(e^{16}>10^4\), \(L\le29.9<\log(10^{13})\). The primitive bracket with upper remainder \(3N!/u^N\) in normalized units holds for all \(u\ge24\), by the same derivative check and separately verified anchor. Verify the closed finite cells in verify.py. This island is carried to B1 unchanged and joined only at the level of the *sign* portfolio, not claimed to propagate its margins through the next finite region.

For an exact lower profile just beyond \(\xi\), use the three counts above. In the part retained from the integer literature computation, if \(n=\lfloor x\rfloor\ge n_0+1\), the sign-based lower baseline can also be kept as the monotonicity increment \(R(x)>e\,\pi(n/e)(x/\log x-n/\log n)\) (on the stated integer-computation domain, including integer \(x\)). This requires no uniform unreported margin from the sieve.

## Certified margin and onset menu

Rows (premise mode,k,log-onset,c) in verify.py (B0 = 0, B1 = 1) mean
\[
 R(x)>\frac{x^2}{L^6}\left(\sum_{j=0}^{k-1}a_j/L^j+c/L^k\right)
 \quad(L\ge\text{log-onset}),
\]
with \(a_0,a_1,\ldots=1,14,145,1412,13985,145450,\ldots\) and empty sum for \(k=0\). Keep the greatest applicable lower bound. B0 rows carry to B1. The \(1+14/L+c/L^2\) bounds at \(L=60\) have different margins; the \(k=2,3,4,5\) fixed-margin rows compare earlier B1 onsets to matching certified B0 onsets. These are sufficient thresholds, not impossibility bounds for B0. Both premises already yield the same connected sign domain.

Let \(C_i=\sum_{j=0}^{\min(i,N-1)}j!\binom{i}{j}-\sum_{j+\ell=i;\,0\le j,\ell<N}j!\ell!\). In \({\cal P}\) the coefficient of \(L^{4-i}\) is \(C_i\); \(C_0,\ldots,C_3=0\), \(C_{4+j}=a_j\) for \(4+j<N\). For \(i>2N-2\), all coefficients are positive. Truncate after \(2N-2\) for a lower bound. In a finite cell \([u,v]\), after subtracting the first \(k\) terms and scaling by \(L^k\), evaluate positive powers of \(1/L\) at \(v\), negative terms at \(u\). For the error use positive powers of \(L\) at \(v\), \(Lf(L),h(L),L/(L-1)\) at \(u\), and \(E\) at its decreasing-branch left endpoint (also admitting the right limit if crossing 58). If a cell crosses the finite sign cutoff, do not use the sign there. A failed cell is bisected and both children must pass. This covers all real points and the ends of every cell.

At \(L\ge\max(320,\text{row onset})\), use only the \(G_b\) transport; the scaled \(L^k{\cal E}(L)\) with this choice decreases for the menu exponents. Transport monomials have rates at least \(1/8\) and degrees at most two, with decreasing factors \(1+1/(L(1-a-2/58))\), \(Lf(L)\), \(L/(L-1)\); for shifted monomials the log derivative contribution of \((L-1)^d\) is \(\le d/(L-1)\). Algebraic \(h\) terms decrease after scaling since \(k+4<12\); the square also decreases after scaling by using decreasing \(w\) and decreasing scaled \(w\). Negative polynomial terms have greatest magnitude at the left endpoint of this tail. Drop remaining positive terms; when \(c\) equals the nominal leading coefficient, test the next scaled residual against zero instead.

For matched-domain pointwise comparison, the B1 clipping decreases \(E\): for fixed \(u\ge58\), \(e^{-au}(1+1/[u(1-a-2/58)])\) decreases in \(a\) for these rates; its logarithmic derivative is \(\le-u+1/[u(1-a-2/58)^2]<0\). The B1 transport strictly beats the CH floor for \(u\ge170\): subtract the common power and anchor correction and check its spectral part at 170 (mertens.py), then use monotonicity. Hence the reconstructed lower functions are strictly ordered for \(L\ge171\). Pointwise extrema handle earlier crossover and the joins with the original sign theorem.

The same primitive method gives any fixed further asymptotic order if needed: use \(N>k+5\), find an integral anchor with the strict remainder bracket (the lower difference grows unbounded by its derivative; the upper-minus-difference does also once \(2(1-(N+1)/u)>1\) stays bounded away from 1), then use the finite rational coefficients and exponential error tail. No higher numeric onsets beyond the replay menu are claimed. A larger \(N\) is not automatically a stronger bound at a fixed small \(L\).
