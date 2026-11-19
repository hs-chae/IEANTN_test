# Ramanujan gap: final real onset and quantitative bounds

Write (t=log x), (N=38358837682), and (kappa=5/32). Two candidates (one uses the contract, the other does not):

1. **A-D02, optimal real onset.** (R(x)>0) for every real (x>X_*), where (X_*) is the unique root in ((N,N+1)) of
   [
     rac{e X_*}{log X_*},632207037 =1644673232^2.
   ]
   Exactly: (38358837682.217926<X_*<38358837682.217927), and (R(X_*)=0). In particular the least integer sufficient onset is (N+1). In addition,
   [
       R(x)>rac{x^2}{t^6}left(1+rac{13}{t}
ight)qquad(tge48.25).
   ]
   The pointwise function in (3) below is another lower bound and gives a sharper asymptotic. On ((X_*,N+1)) the displayed root equation's left side minus its right side is **exactly** (R(x)).
2. **Without A-D02.** (R(x)>0) on ((X_*,e^{753.8}]cup[e^{3041},infty)). On the latter ray one has (R(x)>0.001,x^2/t^6), with (0.08) for (tge3060) and (0.23) for (tge3100). Bounds for more general (t) in these ranges are specified below. These are unconditional in the sense of the admitted papers (finite-height RH is a published verification, not a hypothesis of full RH).

Relative to Platt–Trudgian Theorem 2 the unconditional ray moves from (3915) to (3041) in log scale, the low interval extends from (58) to (753), and the conditional result fills the entire remaining gap. The real left endpoint needs a correction: Theorem 2 literally prints (38358837682<x) on the small interval, which cannot hold on ((N,X_*]). We use its **integer restriction only**, as an admitted original result at its original trust level; no conclusion here uses its incorrect real subinterval. The changed onset is strongest possible for a real positivity ray, not a claim about the absence of earlier disjoint positivity intervals.

## Counting and real endpoints

(pi(N)=pi(N+1)=1644673232), and
(lfloor x/e
floor=14111427770) for (Nle xle N+1); the prime count at that argument is (632207037). To check the counts, (phi(m,a)) in count.py counts integers up to (m) with no factor among the first (a) primes. Removing multiples of the next prime gives its recursive difference. The base rule when (p_a^2>m) counts only 1 and primes above (p_a). With (a=pi(lfloor n^{1/4}
floor)), every remaining composite has two or three prime factors counted with multiplicity. For smallest prime (p_i) (index zero-based) the two-factor count is (pi(lfloor n/p_i
floor)-i); for ordered smallest two (p_ile p_j) the three-factor count is (pi(lfloor n/(p_ip_j)
floor)-j). Their exact limits and the sieve are given in count.py. The inequalities for (e,log x) and the strict bracket signs are rational checks in cert.py. The right-side jump in (R) at (N) is zero; the negative sign extends strictly to (X_*). For an integer (nge N+1), (R(x)ge R(n)) on ([n,n+1)) since (pi(x)=pi(n)) and (x/log x,pi(x/e)) are nondecreasing with (pi(x/e)>0). Thus the integer restriction of the admitted source supplies ([N+1,e^{58}]) on the real line. Dudek–Platt PDF pp. 8–10 (notably §3.1, Lemma 3.4) also records the integer computation up to (10^{11}) and their stepped computation through (1.15cdot10^{16}); those computations are not rerun here.

## A two-sided model for the prime count

Use (a=1.048cdot10^{-12}), (B=115.1), and (lambda=7/48). For (sge20), let
[
 D(s)=a e^{-lambda(s-220)_+},qquad D_U(s)=a .
]
With A-D02 one has (|e^{-s}	heta(e^s)-1|le B e^{-s/2}+D(s)); without it replace (D) with (D_U). Indeed CH2 Corollary 1.3 and the prime-power estimate quoted by Dusart yield the unconditional bound. The contract controls (psi) from (s=220) onward by (A(s)=s^2e^{-kappa s}/64). At 220, (A(220)<a), and ((log A)'=2/s-kappa<-lambda). The original unconditional input is stronger than the new analytic assumption over some ranges; we keep it.

Put (S(t)=sum_{j=0}^8 j!/t^{j+1}) and
[
 r(t)=rac{B e^{-t/2}}{t}left(1+rac{5}{2t}
ight)
       +rac{D(t)}{t}left(1+rac{4}{3t}
ight)
       +rac{2cdot9!}{t^{10}}+2e^{20-t}. 	ag{1}
]
Let (r_U) replace (D) by (D_U). Then (|pi(e^t)e^{-t}-S(t)|le r(t)) for (tge20), with its corresponding assumption, or (le r_U(t)) unconditionally.

For the proof write (d_	heta(s)=e^{-s}	heta(e^s)-1), and let (v=20). Partial summation (atoms at the lower endpoint excluded) and (S+S'=1/t-9!/t^{10}) give
[
 pi(e^t)e^{-t}-S(t)=rac{d_	heta(t)}{t}
  +e^{v-t}[pi(e^v)e^{-v}-S(v)-d_	heta(v)/v]
  +int_v^t e^{s-t}igl(d_	heta(s)/s^2+9!/s^{10}igr),ds. 	ag{2}
]
The bracket has absolute value (<2) since (pi(u)le u), (0le	heta(u)le2u) (Dusart Thm. 4.2) and (S(20)<1/10). If (F(s)) is a positive component of a majorant with (F(s)/F(t)le e^{mu(t-s)}) for (vle sle t), then its integral with (s^{-j}) in (2) is at most (F(t)t^{-j}/(1-mu-j/v)) when the denominator is positive. This follows from (log(t/s)le(t-s)/v) and integrating the exponential. Use ((mu,j)=(1/2,2),(lambda,2),(0,10)), also valid with constant (D_U).

Given any of the radii (r_*=r,r_U,r_L) (the last is below), define the explicit signed lower bound
[
 M_*(x)=x^2left[rac{S(t-1)-r_*(t-1)}{t}
                         -(S(t)+r_*(t))^2
ight]. 	ag{3}
]
It satisfies (R(x)ge M_*(x)) whenever both radii apply. In fact the difference between (t^6R(x)/x^2) and the corresponding main expression with radius zero has absolute value at most
[
 {cal E}_*(t)=t^5r_*(t-1)+(2tS(t)+t r_*(t)),t^5r_*(t). 	ag{4}
]
With the contract this is (O(t^{-5})); in particular the normalized gap is (1+14/t+145/t^2+1412/t^3+13985/t^4+O(t^{-5})). This is a quantified margin, not just an asymptotic used for choosing an onset.

For checking positivity, expand ((1-1/t)^{-(j+1)}) by the binomial series with positive coefficients. Truncation at total degree 18 for the first term gives a lower polynomial in (1/t) for (t^6[S(t-1)/t-S(t)^2]). The coefficients may equivalently be generated using the list (A_k) in cert.py, (2le kle18), with term (A_k/t^{k-6}). Explicitly
(A_k=sum_{0le jlemin(8,k-2)}j!inom{k-2}{j}
-sum_{0le jle8, 0le k-2-jle8} j!(k-2-j)!).
The first nonzero term is 1, then (14/t+145/t^2). Only (A_{17},A_{18}) are negative among the nonzero coefficients, and their contribution for (tge40) is (>-1/t^2). The rational mesh bounds (4) over **closed intervals**, not just sampled nodes: each factor (s^m e^{-
u s}) or (s^m e^{-lambda(s-220)_+}) is bounded using its derivative on the interval, positive polynomial terms evaluated at the appropriate endpoint, and negative ones at the other. For the coefficient 13 we apply this on ([48.25,250]) with the full lower polynomial; on ([250,infty)), (t{cal E}_*(t)) decreases and is (<1) at 250. For the unconditional finite interval the mesh verifies ([43,753.8]), overlapping the source at (e^{58}) and not requiring any extension of the disputed small real endpoint.

## Unconditional large-ray interpolation

Let (Z(s)=2sum_{0<gamma<e^{67}}e^{-(1-eta)s}/gamma) for zeta zeros, multiplicities included. FKS Table 5 at (s=3000,4000) bounds (Z(s)) by the totals (4.968cdot10^{-15},1.103cdot10^{-17}) respectively, rounded outward: their proof bounds the absolute zero sum split into three nonnegative parts at the selected heights (T=t_0^3ge exp(3sqrt{s/5.5666305})>e^{67}). This use of the row is for its **zero-sum components**, not convexity of (|psi(x)-x|). Hölder's finite-sum inequality gives (Z(s)le (4.968cdot10^{-15})exp(-0.0061(s-3000))) on the closed interval. To transfer to all real (x) in that interval, use FKS Theorem 3.2 with its stated parameters ((log x_M,alpha,omega,M)=(40,1/2,0,2.091)) at (T=e^{67}/2.45). Its hypotheses on (T) hold throughout; (T^starle e^{67}) and the relative remainder is (<1.7cdot10^{-25}). If an ordinate equals the fixed cutoff, use a slightly smaller (T) (e.g. by a factor (1-10^{-6})); the strict remainder bound remains valid, and all contributing ordinates are (<e^{67}). No use of the potentially problematic truncated formula identified in FKS Remark 3.3 is needed at this step. The published table entries themselves retain their original computation status.

For (sge4000) use FKS Theorem 1.2, Table 6's (4000) row ((Ale215.823), (R_0=5.5666305)); its upper bound times (s^4) decreases since (s>5.5^2R_0). Add the prime-power correction, giving (|d_	heta(s)|le0.006/s^4) there. Thus on the whole ray (sge3000) a valid majorant is
[
 d_L(s)=max(4.969cdot10^{-15}e^{-0.0061(s-3000)},;0.006/s^4).
]
Use (2) with (v=3000). The bracket is (<8cdot10^{-16}) by (1) unconditionally plus (|d_	heta(v)|/v) evaluated using CH2. The rate ratio for (d_L) holds with (mu=0.0061). The resulting radius is
[
 r_L(t)=rac{d_L(t)}{t}left(1+rac{1.008}{t}
ight)
              +rac{1.004cdot9!}{t^{10}}
              +8cdot10^{-16}e^{3000-t}quad(tge3000).
]
Here (t^5 r_L(t)) is nonincreasing by the displayed shape, so each product in (4) is nonincreasing for (tge3041). The three rational endpoint checks in cert.py imply the stated strict inequalities using the main expression (>1) after normalization. This argument does not address the unconditional window (753<log x<3041).

## Source and verification map

* INPUT_CONTRACT.json, PsiMajorant (hypothetical; all real (xge e^{200})).
* CH2 (arXiv:2512.15709v1), Cor. 1.3 on PDF p. 3, proof §9.1 PDF pp. 35–36. Its finite RH claim is provided by PlattTrudgianFiniteRH Theorem 1.
* Dusart 2018 printed p. 237/PDF p. 11, Thm. 4.2 and **its proof** quoting (0lepsi-	heta<1.4262sqrt x). No external reference imported independently.
* FKS v3, Theorem 1.2 main results, Theorem 3.2/Remark 3.3 PDF pp. 8–9, §4/(4.1)–(4.2), Table 5 PDF p. 22 (3000,4000), Table 6 p. 23 (4000). The zero-free parameter (R_0) is taken with the hypotheses supplied in FKS.
* PlattTrudgian1809.03134v2, Thm. 2 PDF p. 3 and §5 PDF pp. 9–11; DudekPlatt1407.1901v1, Thm. 1.2 (p. 2), Thm. 1.3 and §3.1 (pp. 8–10). Original small-range computation is retained, not represented as a new verified computation.
* Reproduction: `/usr/bin/python3.10 cert.py` checks the rational analytic inequalities and new local counts. Integer and analytic arguments above supply the certificate interpretation, no formal kernel proofs. Numerical values shown for signs by the program are for display only; assertions use exact rationals. Supported argument with original imported results at their paper status.
