# Ramanujan portfolio

Let R(x)=e x π(x/e)/log x−π(x)^2, L=log x, and g(L)=L^6 R(e^L)e^(−2L). All the bounds below are strict on real domains unless expressly stated. The main portfolio is under B0; no result needs D01 (see foundation.md). The basic fallback does not need FKS Table 8. Finite analytic intervals are certified with directed decimal arithmetic, not sampling.

## Results and tradeoffs

1. **Connected positivity ray, with sharp real boundary at inherited finite-computation trust.** Let N=38358837682, A=1644673232, B=632207037. Let r be the unique real root of e B r/log r=A² in [N,N+1]. Then
   [
   N+.217926<r<N+.217927,qquad R(x)>0quad(x>r),qquad R(r)=0.
   ]
   The largest failing integer is N and the least inclusive integer onset is N+1. For r<x≤N+1, R(x)>66000000(x−r). For e.g. x=N+.1 the gap is negative. Thus the literal open real lower endpoint in Platt–Trudgian PNT Theorem 2 cannot be used down to N; see endpoint proof and inherited premise below. The new analytic proof closes the (e^58,e^3915) hole, including all joins. Even without the literature finite sign computation the analytic connected ray below is proved.

2. **Fixed margins.** Each row (v,c) means g(L)>c for every L≥v (v is the logarithm of the real inclusive onset):
   
   | v | c |
   |--:|--:|
   |36.56|0|
   |36.8|.11|
   |37|.20|
   |40|.42|
   |40.23|.50|
   |41|.71|
   |41.15|.75|
   |41.9|.90|
   |42|.92|
   |42.5|1|
   
   For example a sufficient .5-margin onset is e^40.23, while at e^41 the same normalization has margin .71; a .9-margin onset is e^41.9, improved to .92 at e^42 without waiting for e^42.5. These are sufficient, not optimized infima. The basic route gives the entire same table.

3. **Higher profiles.** Set (P_m(L)=sum_{j=4}^{4+m}c_jL^{4-j}), where for all the coefficients used here
   [
   c_j=sum_{i=0}^j i!{jchoose i}-sum_{i=0}^j i!(j-i)! .
   ]
   Thus (P_1=1+14/L), (P_2=P_1+145/L^2), (P_3=P_2+1412/L^3), (P_4=P_3+13985/L^4). The density-enhanced route gives g>P_1 on L≥47.05, and the basic route gives it on [47.05,60] and L≥400. Both routes verify the following *additional compact domains*:
   [
   g>P_2 (52.075le Lle125),quad g>P_3 (57.375le Lle91.50),quad
   g>P_4 (63.50le Lle71.75).
   ]
   Additional whole-ray onsets for g>P_m:
   
   |m|1|2|3|4|5|6|7|8|9|10|11|12|13|
   |--|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
   |L≥|200|225|258|292|327|362|398|434|470|506|542|578|615|
   
   |m|14|15|16|17|18|19|20|21|22|23|24|25|
   |--|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
   |L≥|652|695|730|770|810|850|890|930|970|1010|1050|1100|
   
   The 200 entry for m=1 is used as a join, not a new tradeoff. In basic mode add 200 to the onsets in these two tables. Take the maximum of all applicable bounds and the explicit pointwise lower profile (R3) below. A general extra pointwise early lower bound, without extra sampling, is (R(x)>e B_n[x/log x-n/log n]) for x≥n=floor x≥N+1, with (B_n=pi(n/e)), by inherited integer strictness below the analytic join, and the new Ray theorem above it. Particularly this gives a sawtooth bound, zero at integer x, complementing the early strict sign claim.

## Source and endpoint checks

The original overlapping comparison is PT PNT Theorem 2 (p.3: finite piece then ≥e^3915), Dudek–Platt Theorem 1.2 (p.2: ≥e^9658), and the usable numerical portions of DP §3.1 and Lemma 3.4 (pp.8–10), which do not require RH to perform the finite prime counts. The inheritance actually needed is the finite part of DP: the Galway last failing **prime** below 10^11, reported on p.2, and the numerical sign output of DP Lemma 3.4 on [10^11,1.15·10^16], using only its integer cases. For integers between N+1 and 10^11, the local certificate gives positivity at N+1, and each subsequent prime starts a positive interval up to the next prime by the Galway statement and monotonicity between jumps of π(x). PT's small-domain result has the same required integer cases, but we do not take its literal printed real assertion near N as a premise. DP Theorem 1.3 itself assumes full RH for the infinite tail; that part is not used. The DP real stepping lemma as printed should not be inferred from a bound by ε on the integer count in an arbitrary real interval; for an integer starting point the floor-length bound is valid. We do not claim to have rerun the published long sieve, nor use full RH. If the inherited numerical claim is withheld, discard the connected early result and retain the analytic whole-ray margins and compact domains verbatim.

Check.py and small_end.cpp reverify A and B exactly and prove (lfloor x/e
floor=14111427770) on [N,N+1], and π(x)=A there, so on this closed interval R(x)=eBx/log x−A². The derivative is greater than 66000000 on that interval, and directed arithmetic isolates the zero and gives the negative sign at N+.1. For any other integer n≥N+1, on [n,n+1) π(x)=π(n), π(x/e)≥π(n/e) and x/log x is increasing. Thus positivity at integers propagates to every real point of the ray, with no assumption of constancy of π(x/e) between integers. The early part required here ends before 1.15·10^16, also inside the PT verified integer range. To verify the small-end code, after processing primes <p the count at v excludes integers ≤v with least prime factor already processed (primes themselves retained). The entries greater than 1 surviving with least prime factor p and composite are p times a survivor ≥p, hence the decrement S(floor(v/p))−S(p−1) for v≥p². Decreasing order of v maintains prior-stage values on the right. The domain of distinct floor quotients is closed under division with floor; its two arrays are indexed by small v and large quotient floor(n/j). The differences of successive small counts detect primes, and after p≤√n every composite is excluded.

## Analytic proof

Use the principal-value li(x)=Ei(log x) as in Dusart §5.1, and the li in the finite-height Schoenfeld bounds (not PT PNT paper's separate integral normalized at 2). Dusart Theorem 5.1 proof, p.15, reports π(x)<li(x) below 1.39·10^17. We use this signed input through L=39.47 only. FiniteRH Corollary 1 supplies the two-sided π-error through L=58 in the application domain.

Let J(x)=∑_{p^k≤x}1/k. Partial summation gives (J(x)=psi(x)/L+int_2^xpsi(t)/(tlog^2t)dt). Also
[
 e^{-L}left|int_2^x E(t)/(tlog^2 t)dt+2/log2-operatorname{li}(2)
ight|
 le I(L)=.376 e^{-L/2}/L^2+12cdot10^{-12} e^{-L/8}/L^2+10000 e^{-L}. 	ag{R1}
]
Either sign of the constant is harmless: its abs value is <5. To prove (R1), integrate by parts using D from foundation.md and (w(t)=1/(tlog^2t)). The boundary at x contributes d(L)/L². On [e^16,x], use (1+2/log t≤9/8) and for (a=.5,.875),
(int_{e^{16}}^x t^{a-1}/log^2t,dtle x^a/[L²(a-1/8)]), by differentiating (t^a/log^2t). This yields .376 and at most 12·10^-12 after including the boundary. The integral from 2 to e^16 is bounded for the fractional power contributions using ((1+2/log2)/(log2)^2) and integrating t^(a−1); the resulting sum is <5000. The linear term of D over the full interval contributes ≤2(1/log2+1/log²2) and boundary ≤2/log²2; the endpoint D(2)=−2 gives <3 more. In the expression for (J-mathrm{li}) the actual constant is (2/log2-mathrm{li}(2)), as used in (R1).

For L≥34, by Dusart Corollary 5.2, (x^{1/2}/Lle J-pile 1.2551(x^{1/2}/L+2x^{1/3})). For the upper bound, each term (pi(x^{1/k})/k≤1.2551 x^{1/k}/L), and the number of terms is ≤L/log2<2L. Hence if b bounds (|E|/x), valid normalized upper and lower errors for π are
[
 A_+(L)=(b-e^{-L/2})/L+I(L),qquad
 A_-(L)=[b+1.2551(e^{-L/2}+2Le^{-2L/3})]/L+I(L). 	ag{R2}
]
These mean (operatorname{li}(x)-xA_-lepi(x)leoperatorname{li}(x)+xA_+).
Use the minimum of Ch, Gas and eligible b_q as b, and then take the minimum in (R2) with the finiteRH bound (Le^{-L/2}/(8pi)) where available; for A_+ take zero where the signed result is used. This defines the nonnegative error functions used by check.py on the tested domains. Lower one-sided ψ bounds could omit the coth displacement in Ch but this does not materially alter the onsets.

For n=20, 30 define (l_n(v)=sum_{i=0}^n i!/v^{i+1}) and (u_n(v)=l_n(v)+K(n+1)!/v^{n+2}) with K=5,3 respectively. They bracket e^(−v)li(e^v) for v≥32,80 respectively. Indeed the derivatives of e^v l_n(v) and e^v u_n(v) bracket e^v/v in the appropriate order once (v≥K(n+2)/(K-1)); compare at the anchor by the series
[
 mathrm{Ei}(v)=log v+mathrm{Ei}(-1)+sum_{jge1}(v^j-(-1)^j)/(j,j!),qquad -e^{-1}<mathrm{Ei}(-1)<0.
]
The formula follows by integrating the exponential series with the symmetric principal value at zero. The tails at 32 and 80 use a geometric ratio ≤v/(j+1) and the first omitted term. For n=20 this is <10^-41 at 160 terms; for n=30 the bound at 600 terms is <10^-250. Use the upper bracket for π(x) and lower for π(x/e).

Let (a_i=i!) for i≤n and (a_{n+1}=K(n+1)!). Let (C_{n,j}=sum_{0≤i≤min(n,j)}a_iinom ji-sum_{i+k=j}a_i a_k), with i,k in [0,n+1] in the second sum. The (positive) Taylor terms of l_n(L−1) retain terms up to j=2n+2 in each shifted power, dropping a strictly positive remainder. Multiplying through gives the explicit pointwise bound
[
 g(L)>sum_{j=4}^{2n+2} C_{n,j} L^{4-j}
   -L^5 A_-(L-1)- L^6 A_+(L)[2u_n(L)+A_+(L)]. 	ag{R3}
]
The first four coefficients vanish, the coefficients at 4≤j≤n are exactly c_j, and the domains are L≥33,81 for n=20,30 plus the constraints of (R1)–(R2) (in this report use L≥36.56 for n=20). The upper bound on π is nonnegative, so squaring is justified. Allow the maximum of the two instances where both apply.

For compact certification, check.py uses closed interval cells with all switching points of the explicit A formula as boundaries, including the shift by 1 where needed. At a switch either one-sided choice remains a valid closed-cell bound: signed through 39.47, finiteRH through 58, QRH estimate from its left endpoint. Min and Horner polynomial are evaluated by inclusion intervals. The cell check compares against c or P_m by first dropping exactly the corresponding polynomial coefficients before arithmetic, with scaling L^(m+1). For the main claim, the finite tests go through 200, and basic tests through 340; in basic mode the tests use only P_0 on [60,340] in addition to the separately certified windows. All these compact joins are included.

For infinite tails: by (R2) and checks at 180, whichever cutoff is used,
[
 A_pm(L)le [q(L)+10^{-8}]e^{-L/8}/L
]
on L≥180 in density mode, L≥200 in basic mode, taking q(L)=.005L² in basic mode. The discarded terms after scaling by Le^(L/8) are decreasing and their sum is <10^-8 by the check at 180. For L≥200, u_n(L)<1.04/L and (A_+<.001/L), since q(L)e^(-L/8) decreases in either mode; for the shifted error use (L/(L−1))e^(1/8)<1.14. It follows that after subtracting P_m and scaling by L^(m+1), the two loss terms of (R3) are bounded by
[
 L^{m+5} e^{-L/8}{1.14[q(L-1)+10^{-8}]+2.081[q(L)+10^{-8}]}.
]
This is nonincreasing at every tested tail onset and beyond: in density mode q(L−1) and q(L) decrease; in basic mode expand the polynomial bound or use the log derivative ≤(m+5)/L+2/(L−1)−1/8<0 at all tested onsets. The retained polynomial surplus is bounded below by (C_{n,5+m}) minus the absolute negative-coefficient terms, each divided by (L^{j-5-m}) with j>5+m. This lower bound is nondecreasing. The comparisons at the ray onsets are directed point interval tests; they prove the full infinite tails. For n=30 use it only for m≥16 and the onsets in the second table; the u_n bound there is also checked.

## Attempts, comparison and limitations

The original sign estimates are kept on their valid parts; the connected sign extension and the fixed and higher margins outperform the original *stated* sign results on matched domains, not just a selected later onset. In the early finite-computation part a literal strictly positive real subinterval claimed by PT was instead excluded by counterexample. Original-input black boxes were strengthened by (R1)–(R3), the split QRH zero estimate, and precise li bracketing. These are B0 achievements, so the pointwise matched B0 versus B0+D01 difference is exactly zero, including for any lawful refinements not included here. Finite exact checks on N do not verify the published entire small-domain sieve. Once near the last zero, a uniform positive real margin starting *at* r is impossible. A sharply positive normalized profile throughout the entire inherited finite segment would need quantitative prime counts absent from the sign output, or a substantial new sieve/certified oscillatory calculation. A global order-2 ray beginning at the first compact window is not proved: the finite-height plateau and imperfect control of zeros above it exhaust the small high-order surplus before the exponential-density tail becomes effective. More subdivisions alone do not remove the envelope deficit. The restored exploratory float script is historical and neither its values nor those of the numerical search loop are premises.
