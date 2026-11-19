# Ramanujan gap: connected sign, margins, higher-order profiles

Let \(L=\log x\). With B0, the exact connected real sign conclusion is \(R(x)>0\) for all \(x>\xi\), where
\[
 38358837682.21792636<\xi<38358837682.21792637.
\]
Here \(R(\xi)=0\), and \(\xi\) is the largest real counterexample to strict positivity. The integer sign conclusion begins at \(38358837683\). The connected sign theorem is input-independent (it carries to B1 unchanged); the stronger high-order margins below do use the extra input.

**Correction to the published real endpoint.** Let \(n_0=38358837682\). Platt–Trudgian 1809 PDF p. 3 Theorem 2 prints the range \(n_0<x\le e^{58}\). Read literally for every real number with inclusive \(\pi\), it is false, for example at \(x=38358837682.1\). We retain only its integer restriction and use monotonicity of \(R\) on every half-open interval \([n,n+1)\) with \(n>e\) (constant \(\pi(x)\), nondecreasing \(\pi(x/e)\), increasing \(x/\log x\)). This covers \([n_0+1,e^{58}]\) using the inherited finite statement for integers, and the new quantitative proof covers \([e^{36.73},\infty)\). This fills the gap to the published analytic onset \(e^{3915}\). Dudek–Platt 1407 PDF p. 2 Theorem 1.2 (\(x\ge e^{9658}\)) is subsumed. Their Theorem 1.3 assumes full RH and explicitly says *integer*. The real stepping argument in their Lemma 3.3 writes a bound by \(\varepsilon\) for the number of intervening primes; for general real endpoints the elementary available bound is \(\lceil\varepsilon\rceil\). We do not treat that as an independently corrected/reverified finite computation. If the inherited integer claim is removed, the short new endpoint computation and the analytic ray do not by themselves prove the intervening finite range.

At \(n_0\) and \(n_0+1\) the counts are both \(1644673232\), and throughout their intervening unit interval \(\lfloor x/e\rfloor=14111427770\) with count \(632207037\). Thus \(\xi\) is exactly the unique root of \(632207037 e x/\log x=1644673232^2\) there. The gap is negative at the left endpoint, positive at the right, and strictly increasing on the unit interval. endpoint.py and primecount.cpp certify the counts, signs and bracket; the displayed expression also gives the exact local quantitative profile. The prime count code starts with \(g(w)=w-1\) on all distinct positive quotients \(\lfloor n/i\rfloor\). Before the step at prime \(p\), it counts the primes below \(p\) together with integers \(\ge2\) with no prime factor below \(p\). It subtracts \(g(\lfloor w/p\rfloor)-g(p-1)\) for \(w\ge p^2\), exactly the composites with least factor \(p\). The test \(g(p)>g(p-1)\) detects primes; quotient closure and descending \(w\) ensure use of unmodified subcounts. After processing through \(\sqrt n\), all composites are removed. This is independent of the published finite computation, but only for the three named integer arguments.

## Explicit pointwise lower function

Set \(N=12,\ f(u)=\sum_{j=0}^{N-1}j!/u^{j+1},\ h(u)=2N!/u^N\). Using PV \(\mathrm{li}\), for \(u\ge30\),
\[
 e^u f(u)< \mathrm{li}(e^u)<e^u(f(u)+h(u)/u).
\]
The difference has derivative \(N!e^u/u^{N+1}\) with respect to \(u\); the proposed upper remainder has derivative at least this for \(u\ge30\). Check strict initial inequalities in verify.py by the convergent series \(\mathrm{li}(e^u)=\gamma+\log u+\sum_{j\ge1}u^j/(j\,j!)\). Its integration constant is \(\lim_{a\downarrow0}(-\int_a^\infty e^{-t}dt/t-\log a)=\gamma\). This follows by writing \(H_n=\int_0^n(1-(1-t/n)^n)dt/t\), subtracting \(\log n\), and taking dominated limits on \([0,1]\) and \([1,\infty)\). The gamma enclosure \(H_n-\log n-1/(2n)\le\gamma\le H_n-\log n-1/(2n)+1/n^2\) follows by the trapezoid rule for \(1/t\) on each \([j,j+1]\) (error \(\le\sup |f''|/12\) by integrating the linear interpolation error).

Write \(d(u)=ue^{-u}(\pi(e^u)-\mathrm{li}(e^u))\) and \(z(u)=e^{-u}\theta(e^u)-1\). For \(u\ge t\) the exact finite-anchor identity is
\[
 d(u)=z(u)+\frac ut e^{t-u}[d(t)-z(t)]
                 +u\int_t^u e^{v-u}\frac{z(v)}{v^2}\,dv. \tag{R1}
\]
It holds with inclusive prime counts, including jump endpoints. Use one-sided caps \(-E_-(u)\le d(u)\le E_+(u)\).

**Repaired finite transport, \(24\le u\le58\).** The printed third line of Platt–Trudgian finite RH, Corollary 1, PDF p. 4, is \(\sqrt{x}\log^2 x/(8\pi)\), not a single log. Thus a direct normalized upper bound for *either* side is \(u^3 e^{-u/2}/25.1327412\). No full RH estimate is used. The original smaller normalized bound was unjustified on this range and is removed. The independent review also showed its eight original early tests need more than just substituting the printed bound. The following independent derivation gives stronger usable caps:

* The exact quotient prime counter at log anchor 24 gives \(\lfloor e^{24}\rfloor=26489122129\), \(\pi(e^{24})=1154106844\). Checked with the PV series, \(-.000007745<d(24)<-.000007744\). By finite \(\theta<x\) and CH2 Lemma 9.2 plus Dusart Corollary 4.5, \(-B_{24}\le z(24)\le0\) where \(B_{24}=1.751000147 e^{-12}+1.78 e^{-16}\). Hence the signed anchor caps for \(d(24)-z(24)\) are \(-.000007745\) and \(B_{24}-.000007744\).
* For any cap \(\sum c v^d e^{-av}\) for one signed side of \(z(v)\) on \([t,u]\), with \(c\ge0,d\ge0,1-a-2/t>0\), use its transport 
\[
 {\cal T}_t[(c,d,a)](u)=c u^d e^{-au}\left(1+\frac{1}{u(1-a-2/t)}\right).
\]
This bounds the endpoint plus integral from (R1): the log derivative of \(e^v v^{d-2}e^{-av}\) is at least \(1-a-2/t\), so its past integral is at most its current value divided by that rate. For the finite-RH \(\theta\) bound \(v^2e^{-v/2}/25.1327412\), integrate \(e^{v/2}\) exactly after cancellation of \(v^2\), dropping the negative lower endpoint; its transport is bounded by \((u^2+2u)e^{-u/2}/25.1327412\).
* Additional \(\theta\) bounds in (R1) come from CH2 Corollaries 1.2–1.3 (PDF p. 3). For \(T=10^7\,2^j\), \(0\le j\le10\), write \(r=\log(T/2\pi)\). The symmetric radius about the CH2 center is \(\pi/(T-1)+(r^2/(2\pi)-r/(6\pi))e^{-v/2}\), with center shift in \([0,(\pi/T)^2/3]\) by the coth inequality in the proof of CH2 Cor. 1.3. We have \(T<e^{24}\) and \(10^9<e^{24}\). For the lower \(\theta\) side add the Dusart prime-power upper correction and drop the nonnegative center shift. For the upper side add the upper center shift but no prime-power correction. In the CH2 symmetric Cor. 1.3 option the center shift is zero. Add the appropriate signed anchor cap times \(ue^{24-u}/24\) to each transport; intersect these and the direct finite \(\pi\) interval. All competing cap functions decrease on \([24,58]\). Numerical CH coefficients are rigorous intervals via the Machin \(\pi\) enclosure and logarithm; one may use their exact symbolic values.

**Later transport, \(u>58\).** Use the minimum of the transports with \(t=58\) of \(B(v)+\mathrm{POWER}(v)\), where \(B=C,G_{7/8}\), and also \(G_{27/32}\) in B1. Here \(\mathrm{POWER}(v)=1.000000147e^{-v/2}+1.78e^{-2v/3}\), and \(C,G_b\) are in common.md. Add \((2\cdot58/25.1327412)u e^{29-u}\) to each transport for the anchor. This uses \(58^2e^{-29}/25.1327412\) for \(|z(58)|\) from finite RH and the **same numerical bound** for \(|d(58)|\) from the new log-24 transport, **not** from the printed \(\pi\) estimate. In fact the two transported signed caps are each \(<3.145\cdot10^{-11}\) at 58, strictly below \(58^2e^{-29}/25.1327412\), as verified by repair_anchor.py. Both sides can use this same later bound. The finite formulas apply at 58, and cells crossing 58 (or 59 for the shift) admit the right limit. Thus there is no unsupported finite join. All caps are positive and nonincreasing within their stated branches.

For \(L\ge30\), let \(w=h+E_+\), except use \(w=h\) through \(L=43.74\) by the finite upper sign \(\pi<\mathrm{li}\). Put
\[
 {\cal E}(L)=L^4\{[L/(L-1)]E_-(L-1)+2Lf(L)w+w^2\}.
\]
Then
\[
 \frac{L^6 R(x)}{x^2}>{\cal P}(L)-{\cal E}(L),\qquad
 {\cal P}(L)=L^6[f(L-1)/L-f(L)^2].
\]
The lower bound for \(\pi(x/e)\) uses \(f(L-1)\); the upper for \(\pi(x)\) uses \(f(L)+w/L>0\), so squaring introduces no sign error. The neglected lower \(\mathrm{li}\) remainder is strictly positive. This rational-algebraic main term with explicit exponential error is an output, not the constant 1 alone. It also permits using exact finite-source constants and endpoints, retaining source sign wherever stronger, and signed transports of source intersections using the same identity. In a signed transport use the corresponding upper/lower endpoints in the integral and anchor from any eligible fixed point. Use the offset if directly comparing differently normalized \(\mathrm{li}\).

### Earlier finite quantitative island (B0)

The older finite sign result does not give a uniform quantitative margin. For each row \((u,c)\) in the following list, \(R(x)>c\,x^2/L^6\) for \(u\le L\le30.933\):
\[
 (27.90,.010),(27.91,.015),(28,.069),(28.88,.50),
 (28.95,.53),(29,.554),(30,.88).
\]
These seven improvements preserve both prior islands. This uses the CH2 Lemma 9.2 *lower* bound \(\delta(v)\ge-.751e^{-v/2}\) and the Dusart power correction. Apply the signed anchor identity at 16, keep the upper sign \(\pi(x)<\mathrm{li}(x)\), and in the lower \(\pi\) error drop the nonnegative \(-z(16)/16\) inside the anchor. The lower error is thus bounded by the transport of \(1.751000147 e^{-v/2}+1.78e^{-2v/3}\), with anchor contribution \((.000396122/16)u e^{16-u}\) (the exact inclusive count \(595341\) at \(e^{16}\) and the PV series certify \(d(16)>-.000396122\)) and the factor \(1+1/[u(1-a-2/16)]\) for each term. All used finite source arguments are inside their domains: \(e^{16}>10^4\), \(L-1\le29.933<\log(10^{13})\); only the shifted argument uses CH2 Lemma 9.2. The primitive bracket with upper remainder \(3N!/u^N\) in normalized units holds for all \(u\ge24\), by the same derivative check and separately verified anchor. Verify the closed finite cells in verify.py. This island is carried to B1 unchanged. No positive analytic bridge is claimed between the island and log 36.73; the inherited integer conclusion supplies the connected sign on that interval.

For an exact lower profile just beyond \(\xi\), use the three counts above. In the part retained from the integer literature computation, if \(n=\lfloor x\rfloor\ge n_0+1\), the sign-based lower baseline can also be kept as the monotonicity increment \(R(x)>e\,\pi(n/e)(x/\log x-n/\log n)\) (on the stated integer-computation domain, including integer \(x\)). This requires no uniform unreported margin from the sieve.

## Certified margin and onset menu

Rows (premise mode,k,log-onset,c) in verify.py (B0 = 0, B1 = 1) mean
\[
 R(x)>\frac{x^2}{L^6}\left(\sum_{j=0}^{k-1}a_j/L^j+c/L^k\right)
 \quad(L\ge\text{log-onset}),
\]
with \(a_0,a_1,\ldots=1,14,145,1412,13985,145450,\ldots\) and empty sum for \(k=0\). Keep the greatest applicable lower bound. B0 rows carry to B1. The \(1+14/L+c/L^2\) bounds at \(L=60\) have different margins; the \(k=2,3,4,5\) fixed-margin rows compare earlier B1 onsets to matching certified B0 onsets. These are sufficient thresholds, not impossibility bounds for B0. Both premises already yield the same connected sign domain. The independently certified analytic sign ray is now \(L\ge36.73\). All eight prior early margin statements are recovered at their original or strictly better onsets, using the corrected proof, and strengthened at their original onsets. In particular .001, .009, .41, .92, 1 begin at 36.74, 36.76, 37.70, 39.66, 40.16; at the former 36.984, 37, 38, 40 the stronger margins .130, .137, .515, .976 apply. In the \(1+c/L\) family the same prior margins 4, 10, 14 begin at 40.92, 45.10, 47.20, and the stronger same-onset values 5.4 at 43 and 12 at 46 also apply. Only the corrected proof, not the historical calculation, supports these timings.

Let \(C_i=\sum_{j=0}^{\min(i,N-1)}j!\binom{i}{j}-\sum_{j+\ell=i;\,0\le j,\ell<N}j!\ell!\). In \({\cal P}\) the coefficient of \(L^{4-i}\) is \(C_i\); \(C_0,\ldots,C_3=0\), \(C_{4+j}=a_j\) for \(4+j<N\). For \(i>2N-2\), all coefficients are positive. Truncate after \(2N-2\) for a lower bound. In a finite cell \([u,v]\), after subtracting the first \(k\) terms and scaling by \(L^k\), evaluate positive powers of \(1/L\) at \(v\), negative terms at \(u\). For the error use positive powers of \(L\) at \(v\), \(Lf(L),h(L),L/(L-1)\) at \(u\), and \(E\) at its decreasing-branch left endpoint (also admitting the right limit if crossing 58). If a cell crosses the finite sign cutoff, do not use the sign there. A failed cell is bisected and both children must pass. This covers all real points and the ends of every cell.

At \(L\ge\max(320,\text{row onset})\), use only the \(G_b\) transport; the scaled \(L^k{\cal E}(L)\) with this choice decreases for the menu exponents. Transport monomials have rates at least \(1/8\) and degrees at most two, with decreasing factors \(1+1/(L(1-a-2/58))\), \(Lf(L)\), \(L/(L-1)\); for shifted monomials the log derivative contribution of \((L-1)^d\) is \(\le d/(L-1)\). Algebraic \(h\) terms decrease after scaling since \(k+4<12\); the square also decreases after scaling by using decreasing \(w\) and decreasing scaled \(w\). Negative polynomial terms have greatest magnitude at the left endpoint of this tail. Drop remaining positive terms; when \(c\) equals the nominal leading coefficient, test the next scaled residual against zero instead.

For matched-domain pointwise comparison, the B1 clipping decreases the later radii: for fixed \(u\ge58\), \(e^{-au}(1+1/[u(1-a-2/58)])\) decreases in \(a\) for these rates; its logarithmic derivative is \(\le-u+1/[u(1-a-2/58)^2]<0\). The B1 transport strictly beats the CH floor for \(u\ge170\): subtract the common power and anchor correction and check its spectral part at 170 (mertens.py), then use monotonicity. Hence the reconstructed lower functions are strictly ordered for \(L\ge171\). Pointwise extrema handle earlier crossover and the joins with the original sign theorem.

The same primitive method gives any fixed further asymptotic order if needed: use \(N>k+5\), find an integral anchor with the strict remainder bracket (the lower difference grows unbounded by its derivative; the upper-minus-difference does also once \(2(1-(N+1)/u)>1\) stays bounded away from 1), then use the finite rational coefficients and exponential error tail. No higher numeric onsets beyond the replay menu are claimed. A larger \(N\) is not automatically a stronger bound at a fixed small \(L\).


## Additional orders and sharper high-order pointwise profiles

Use \(N=20\) instead of 12 in the displayed \(f,h,{\cal P}\) formulas, for \(L\ge53\). The log anchor is 52 for both bounds on \(\mathrm{li}\); the derivative proof applies since \(2(1-21/u)>1\) for \(u\ge52\). In the finite series for that anchor use 280 terms: for \(u\le52\) the ratio of terms after 280 is \(<1/5\), and the omitted sum is below one fourth of the last term. At \(u\ge52\) the 20-term lower primitive is strictly larger and its upper primitive strictly smaller than the old ones. For the upper comparison divide both proposed increments after \(f_{12}\) by \(12!/u^{13}\) and check the sum for \(j=12,\dots,19\) plus the 20-term remainder is \(<2\) at 52; every summand is nonincreasing thereafter. Taking the maximum of all valid lower profiles retains the former ray and islands.

For \(u>58\) also admit the \(t=58\) transports of the sharper positive spectral mixture from enhanced.md (replace \(D_i\) by \(D_4(s_i)\), keep the .001 mesh and drop all negative endpoint corrections in the mixture used here). All validity and derivative calculations for the older positive mixture apply. In particular this replaces, but need not discard, its previous transport. The pointwise smaller transport follows by writing the mixture as \(D_4(s_0)\) times the weight at \(s_0\) plus the discrete positive increments of the weight times \(D_4(s_i)\). The weight \({\cal T}_{58}[(1,0,1-s)](u)\) is increasing in \(s\) on this strip. The proof uses exactly the same 58 anchor bound.

The following further **whole rays** use the same profile convention, with the \(a_j=C_{4+j}\) for \(N=20,\ 4+j<20\). They are proved by higher.py. Thresholds are sufficient, not minimal.

| \(k\) | \(c\) | B0 log-onset | B1 log-onset |
|---:|---:|---:|---:|
|6|1500000|348|284|
|7|18000000|385|312|
|8|200000000|409|329|
|9|2800000000|446|357|
|10|37000000000|478|381|
|11|500000000000|510|405|
|7|19063832|390|315|
|8|241691425|426|341|
|9|3277187246|462|368|
|10|47424796805|498|395|
|11|730550160076|534|422|
|12|11946592513217|571|449|
|13|206824220948690|607|477|
|14|3780755108724421|646|506|

The last eight rows take \(c=a_k\). There we subtract the first \(k+1\) terms, scale by \(L^{k+1}\) and check strict positivity rather than bounding \(a_k\) minus an error directly. The next coefficient is positive (including \(a_{15}=72793555607972000\)). In each tail certificate discard all subsequent positive terms, put subsequent negative terms at the onset, and bound the scaled error there: the log derivative of the power-exponential part is at most \((k'+4)/L+2/(L-1)-1/8<0\), where \(k'=k\) or \(k+1\). The factor \(L^{k'+4}h(L)\) decreases since \(k'+4<20\); the other factors used in the error are positive decreasing as in the earlier tail check. This proves the entire rays directly, without an untested finite interval. At the B0 onsets for the first six rows, B1 already admits the full \(a_k\) coefficient for \(k=7,\ldots,11\) by the later block (and the older results supply separate \(k=6\) tradeoffs). No constant \(c>a_k\) is possible in this exact fixed-order, fixed-prior-coefficients whole-ray shape: the same two-sided primitive bracket and exponential bound give \(L^k[L^6R/e^{2L}-\sum_{j<k}a_j/L^j]\to a_k\). For the displayed \(k\le14\), \(k+4<20\) removes the normalized remainder; the binomial expansion is absolutely convergent and the next-order polynomial terms vanish. This optimality is only for the coefficient in that restricted shape, not for the onsets or for general lower functions.

For original-source comparison one may additionally take any applicable lower/upper bounds \(p_-(x/e),p_+(x)\) on \(\pi\) from common.md, transporting the stated normalizations, and use
\[
 R(x)\ge e x\,p_-(x/e)/L-p_+(x)^2
\]
with \(p_+\ge0\); the maximum includes the inherited integer-based increment and the independently corrected local formula. All B0 branches carry to B1. Strict quantitative cross-mode comparisons refer to the stated pointwise transported branch and the certified profile menu, not to an impossibility theorem for any deduction from B0.


### Fixed-onset and fixed-margin comparison at order two

For a further pointwise option take the anchor \(t=100\) and \(\theta\) radius \(G_4^+(v)+\mathrm{POWER}(v)\) on \(v\ge100\) (here use the .001 mesh). The bound for the signed anchor magnitude \(|d(100)-z(100)|\) is the old \(C\)-transport of \(|d(100)|\) plus \(C(100)+\mathrm{POWER}(100)\). For all positive monomials apply \({\cal T}_{100}\). For the special subtracted background \(r(v)=(v^2/48-54-D_4(.77))e^{-.23v}\), one has
\[
 e^v r(v)/v^2=e^{.77v}\left[1/48-(54+D_4(.77))/v^2\right],
\]
with positive increasing bracket. Thus the relevant log derivative is at least .77, giving transport \(r(u)(1+1/(.77u))\); the background itself is nonincreasing from 100 as checked in enhanced.md. This transfer is based on the positive background after subtraction, not on subtracting unrelated upper estimates for integrals. It is combined by minimum with the other valid radii. The entry at 100 can only reduce the bound.

Using the resulting pointwise bounds with \(N=20\), for \(L\ge60\) the \(1+14/L+c/L^2\) profile holds with \(c=19.85\) in B0 and \(c=81.8\) in B1. At fixed \(c=120\) the sufficient log-onsets are 202 versus 175, and at \(c=145\) they are 217 versus 186. The check uses closed cells of width \(1/10\) through 320, both halves of a bisected cell when necessary, and the shared tail criterion with \(k'=3\) for the exact \(c=a_2=145\). The older thresholds are kept, not misreported as lower bounds on what B0 can do.
