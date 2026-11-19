# Ramanujan gap

Let \(L=\log x,\ f(v)=e^{-v}\operatorname{li}(e^v)\) with the PV normalization, and \(R=(ex/L)\pi(x/e)-\pi(x)^2\). Define
\[
 c_n=\sum_{k=0}^{n-2}\big[k!{n-2\choose k}-k!(n-2-k)!\big],
 \qquad F_j(L)=\sum_{n=6}^{6+j}c_nL^{6-n}.
\]
Thus \(F_0=1\) and successive nonconstant coefficients are \(14,145,1412,13985,145450,1610021,19063832,241691425,\ldots\).

## Main conclusions

All onsets in the table are \(\log x\), closed, and the lower bounds are strict:
\(R(x)>(x^2/L^6)F_j(L)\). B0 and B1 are defined in common.md.

| j | B0 certified onset | B1 certified onset |
|---:|---:|---:|
|0|42.8|42.8|
|1|47.5|47.5|
|2|222|188|
|3|255|212|
|4|289|238|
|5|324|264|
|6|359|290|
|7|395|316|
|8|431|343|
|9|467|370|
|10|503|397|
|11|539|424|
|12|575|451|
|13|612|478|
|14|648|506|
|15|684|533|
|16|721|560|

The tuned density weights are used in this table. Keep B0 **finite** \(F_2,F_3,F_4\) branches on \(53\le L\le120,\ 58\le L\le91,\ 64\le L\le71.5\), respectively. These finite windows and the final rays need not connect. At first the uniform-density reconstruction left a gap in the B0 \(F_1\) ray (finite branch on \([48,170]\), late onset 192); B1 closed it, but the refined B0 calculation closes it too. Do not credit D02 for that improvement. B1 still advances the higher-profile onsets. At \(L=200\) the displayed B1 ray has \(F_2\) versus \(F_1\) for the B0 reconstruction. At \(L=290\) use \(F_6\) versus \(F_4\), and at \(L=400\), \(F_{10}\) versus \(F_7\). These margin comparisons describe the certified profiles, not exclusions for B0.

In B0 constant normalized margins \(0.005,0.05,0.25,0.60,0.84,1\) hold on the respective full closed rays \(L\ge37.2,39.4,39.9,40.9,41.9,42.8\). Retain \(0.06\) on \(37.2\le L\le39.3\) as a separate stronger finite branch. One cannot demand a fixed constant \(>1\) on any full final ray: (1) or (2) in common.md, partial summation and the factorial expansion below give limit 1.

The B0 density-free \(F_0\) and connected sign results below do not use the FKS density table. The main additional improvement is quantitative: **no B1 improvement to the connected ray of strict sign is possible**, since its endpoint is the actual largest real failure (under the inherited finite computation).

### Exact last failure; correction of a real endpoint

Write \(n=38358837682\), \(p_*=14111427770\). The exact counts are \(\pi(n)=1644673232,\ \pi(p_*)=632207037\). On \([n,n+1)\), \(\lfloor x\rfloor=n,\ \lfloor x/e\rfloor=p_*\). The unique root \(r\) there of
\[
 e\,r\,632207037/\log r=(1644673232)^2
\]
lies strictly between \(n+0.2179263651\) and \(n+0.2179263652\). Indeed this left side increases, and endpoint.py verifies both local signs, the floors, and \(R(n)<0\). Therefore \(R(x)\le0\) on \([n,r]\), with equality only at \(r\) there. In particular the literal wording “all \(n<x\le\exp(58)\)” in PT 1809.03134v2 Thm. 2 (PDF p. 3) cannot be used as a true real statement. Neither that literal real theorem nor its proof is needed for the large finite join. Use Dudek–Platt's expressly reported *integer* last failure up to \(10^{11}\) (PDF p. 8, §3.1 first paragraph) and the integer portion of their reported computation through \(1.15\cdot10^{16}\) (Table 1, Lemma 3.4, PDF pp. 9–10). These are at inherited finite-computation trust; the computation in Lemma 3.4 is not conditional on full RH, despite its placement in the RH section. In particular do not use their full-RH analytic continuation of that finite result. For each covered integer \(k>n\), \(R\) is nondecreasing from \(k\) to \(k+1\) with the latter excluded: \(\pi(x)=\pi(k)\) and \(\pi(x/e)\) and \(ex/\log x\) are nondecreasing. This gives the real join \([n+1,1.15\cdot10^{16}]\). Our signed π, finite-height, and CH2 bounds give \(R>0\) already on \(36.95\le L\le37.2\) (checks.py, which also checks \(36.95<\log(1.15\cdot10^{16})\)), and the quantitative rays complete the proof. The largest real failure is \(r\), while \(n\) is the largest integer failure. Strict sign holds on \((r,\infty)\), not at \(r\). A rational closed onset is \(n+0.2179263652\). This locally verified repair addresses the integer-vs-real wording; it does not rerun the original large finite prime computation.

The local count algorithm starts with \(S(v)=v-1\) for every distinct \(v=\lfloor n/i\rfloor\) (separately for each count). Sieve primes in increasing order through \(\sqrt n\), recognizing each \(p\) by \(S(p)>S(p-1)\). The surviving set contains smaller primes and integers not divisible by any smaller prime. For \(v\ge p^2\) exactly \(S(\lfloor v/p\rfloor)-S(p-1)\) current survivors have smallest prime factor \(p\) and are composite; remove them. Process \(v\) in decreasing order, so the smaller index has its old value. Quotient indices are closed under nested division, and all integers through \(\lfloor\sqrt n\rfloor\) occur. Finally only primes remain. All comparisons of the analytic root are via outward arithmetic, not an approximate root finder.

## Proof of the analytic profiles

For \(v\ge31\) put
\[
 P(v)=\sum_{k=0}^{24}k!/v^{k+1},\qquad P^+(v)=P(v)+K/v^{26},
 \quad K=25!/(1-26/31).
\]
Then \(P(v)\le f(v)\le P^+(v)\): \(f'+f=1/v\), and the two are a sub- and supersolution of this differential equation. The anchor brackets at 31 follow from the absolutely convergent series \(\operatorname{Ei}(v)=\gamma+\log v+\sum_{k\ge1}v^k/(k\,k!)\) (termwise derivative and PV normalization, or expansion at \(0^+\)). To identify the constant, integrate \((e^t-1)/t\) from 0 and use the PV definition: \(\lim_{z\downarrow0}(\operatorname{Ei}(z)-\log z)=\int_0^1(1-e^{-t})dt/t-\int_1^\infty e^{-t}dt/t=\gamma\). The last identity follows by writing \(H_n=\int_0^n [1-(1-t/n)^n]dt/t\) and applying dominated convergence after subtracting \(\log n\). The anchor uses only \(0.57<\gamma<0.59\) from the harmonic sum at 100. The series beyond degree 180 at 31 is at most twice its first omitted term.

Here is the transfer used for the π error. If \(|\theta(e^v)e^{-v}-1|\le\sum_i c_i v^{k_i}e^{-d_iv}=D(v)\) for \(v\ge a\), with \(c_i\ge0,\ k_i\in\{0,2\},\ d_i\le1/2\), then
\[
 |\pi(e^v)e^{-v}-f(v)|
 \le e^{a-v}(P_a+D(a)/a)+
 \sum_i c_i v^{k_i-1} e^{-d_iv}\left(1+\frac1{v(1-d_i-2/a)}\right).
 \tag{6}
\]
Here \(P_a\) bounds the normalized π error at the anchor. Partial summation gives the endpoint plus the past integral, with anchor contribution from both π and θ; the derivative of \(\log(e^{(1-d_i)u}u^{k_i-2})\) is at least \(1-d_i-2/a>0\). This proves (6) also at the anchor and for every real between anchors.

The certificate uses CH2 all-domain θ \(A+116e^{-v/2}\) at \(a=50\), and adjustable finite-height CH2 θ \(a_T+(C_T+2)e^{-v/2}\), from \(a=24\) for \(T\le10^{10}\) and \(a=29\) otherwise. The finite-RH π error bounds \(P_a\) at these anchors. For \(v\le58\) the direct finite-RH π branch supplies \(v e^{-v/2}/(8\pi)\); for the upper error use 0 when \(v\le39.3\) in the reported early domain, by Dudek–Platt Lemma 3.2 proof, PDF p. 8, which states \(\pi(x)<\operatorname{li}(x)\) up to \(1.2\cdot10^{17}\). For the density transfer take \(a=61\), \(D=E_b^\theta\), and the CH2 \(a=50\) transfer for \(P_{61}\). The short-join test for \(F_1\) also uses \(D=C_b(160)e^{-(1-b)v}\), \(a=160\), and a CH2 anchor. Optional comparison envelopes can integrate the minimum input instead of bounding the full integral by each individual branch.

Write \(U(v),V(v)\) for upper/lower absolute π allowances (use \(U=0\) on the signed interval). On the domains checked, \(P^+(L)\le1.03/L,\ U(L)<0.01/L\). The first follows by checking at 37 and decreasing terms; for the second, the CH2 branch at \(T=2\cdot10^8\) already gives the bound at 37, and \(v\) times this allowance decreases for \(v\ge37\) apart from a constant, by (6). The tail allowances themselves easily satisfy the same inequality at the tested anchors and decrease after multiplication by \(v\); the certificate's linear loss bound can equivalently be applied to the minimum of that CH2 branch and the tail allowance. Thus normalized loss from the Li proxy is at most
\[
 L^5\left[V(L-1)+2.07\,U(L)\right].
\]
For a lower bound on the proxy itself, expand \(P(L-1)/L\) by the binomial series in \(1/L\) through exponent 26 (all dropped terms positive), and subtract \((P^+(L))^2\). Multiply by \(L^6\). Call the unscaled polynomial coefficients \(D_n\). For \(2\le n\le26\) the coefficient formula above applies; \(c_2,\ldots,c_5=0,\ c_6=1\). For \(N=j+7\), the excess above \(F_j\), multiplied by \(L^{j+1}\), is at least
\[
 D_N+\sum_{n>N}\min(0,D_n)a^{N-n}\qquad(L\ge a).
\]
For finite cells use positive terms too, at their right endpoints, and negative terms at their left endpoints. This derives the certificate's exact slack tests; it is not a numerical evaluation of the true gap followed by extrapolation.

On an entire tail \(L\ge a\), multiplying the error by \(L^{j+1}\) produces nonnegative terms decreasing if \((j+6)/a+1/(a-1)<1/8\). This follows by logarithmic differentiation of (6), since all density tail rates are \(\ge1/8\), the maximum positive power at \(L-1\) is 1, and reciprocal factors only help. The same suffices for (3) of common.md and for the direct D02 transfer. Hence each positive slack test **at the onset** proves its whole tail. For earlier intervals use (6), and the direct finite bounds, all decreasing on their cells; evaluate the normalized positive powers at the right endpoint and all upper-error multipliers at the left. Choose only branches available throughout a cell, in particular handle \(39.3,58,59\) separately. The finite tests cover \([42.8,60]\) for \(F_0\), then \([60,280]\) by CH2 alone, and \([280,\infty)\) with the no-density QRH bound. The finite \(F_1\) checks cover B0 \([47.5,170]\), then refine.py joins \([170,190]\) to its refined B0 tail. For this join it uses (6) with the refined θ majorant at 61 and the global CH2 allowance, taking the minimum. B1 retains that ray. The earlier constant-margin tests overlap the \(F_0\) ray. All finite cells are certified ranges, not sample points.

The additional density-free onsets for j=1,2,4,8 are respectively 312,347,421,570 in B0 and 227,254,309,421 in B1; use (3) in B0 and the direct D02 θ bound with anchor 200 in B1. Separately, an explicit pointwise comparator takes the supremum of all applicable profiles, the new exact local formula, and the Li proxy lower bound with the smallest applicable allowance on each of \(\pi(x),\pi(x/e)\); retain the original positivity wherever verified. For the best pointwise analytic transfer in this construction, integrate the pointwise minimum of the θ majorants from a common anchor, rather than integrating each separately, and include direct finite-RH and PT Cor. 2 π bounds with their domains/normalizations. This gives monotone B0-to-B1 comparison on the whole domain, including all joins, since these are valid simultaneous inputs and the B0 branches are retained.

For a further all-ray comparison of the Li-proxy construction alone, the B0 θ endpoint allowance on \(v\ge170\) has a lower bound on its **bound value** \(q(v)\) as in mertens.md. Past-integral and anchor allowances are nonnegative, so the normalized B0 π allowance derived this way is at least \(q(v)/v\) (tiny signed prime-power shifts do not change a comparison by a factor .99). The new refined π allowance of (6) is \(<.99q(v)/v\) at 170 (checks.py), and remains so thereafter: multiply (6) by \(v\) and separately by \(v e^{v/8}\) and differentiate each term, using \(v(5/32-1/8)>2\). The original PT Cor. 2 direct π allowance where active is also larger, by its slower decay and direct left comparison at 2000. Thus on \(L\ge171\) the simultaneous improvement at both arguments strictly raises the Li-proxy lower bound against these B0 branches, even outside the tabulated polynomial comparisons.

## Comparison and limitations

The old \(R>0\) ray from \(L=3915\) (PT 1809.03134v2 Thm. 2), the weaker \(L=9658\) (Dudek–Platt Thm. 1.2, PDF p. 2), and the corrected early real range are included, not used as the only baseline. The direct π bounds from Dusart Thm. 5.1 and Cors. 5.2–5.3 can also be intersected on their stated domains in the general pointwise portfolio. Unconditional here means at **original B0 trust**, including the QRH paper; none of the claims assumes full RH. Comparing against the B0 density construction is substantially more stringent than comparing D02 against a stretched exponential. The connected sign repair is already a B0 theorem; later quantitative profiles are where B1 helps. Positivity under finite RH cannot transmute into full RH. An even sharper quantitative margin close to \(r\) requires the actual discontinuities of \(\pi\) on that enormous finite range or better signed estimates; the shrinking true local gap at \(r\) precludes any positive constant normalized margin all the way down to it.
