# Mertens products and prime sums

Write (t=log x). Let
[
 U(x)=sum_{ple x}1/p-log t-M,qquad
 J(x)=sum_{ple x}(log p)/p-t+B_3 .
]
The constants (M,B_3) have exactly Dusart's definitions (Theorems 5.6 and 5.7; no change of normalization). Let (L_P=e^gamma tP(x)), (L_Q=e^{-gamma}Q(x)/t).

## Results

**Finite-plus-analytic candidate without PsiMajorant or QRH.**
All bounds below are strict. In each column use the coefficient of the last applicable row, including the displayed lower endpoint. Product bounds refer to (max(|L_P-1|,|L_Q-1|)le c/t^3); for (|U|) use (c/t^3), and for (|J|) use (c/t^2).

| Products: onset | (c) | Prime reciprocals: onset | (c) | Log-weighted reciprocals: onset | (c) |
|---:|---:|---:|---:|---:|---:|
| 2278381.712 | .2 | 2278382.114 | .2 | 912559.998 | .3 |
| 2278382 | .19998 | 2278383 | .19995 | 912560 | .2999995 |
| 3500000 | .160 | 3500000 | .160 | 912566 | .299 |
| 5100000 | .148 | 5100000 | .148 | 1200100 | .275 |
| 13000000 | .100 | 13000000 | .100 | 1515100 | .260 |
| 20000000 | .090 | 20000000 | .090 | 1526800 | .230 |
| | | | | 2276000 | .220 |
| | | | | 2278382 | .216 |
| | | | | 3500000 | .172 |
| | | | | 5100000 | .160 |
| | | | | 18100000 | .100 |
| | | | | 35000000 | .090 |

At the original coefficients ((.2,.2,.3)), the best real **closed** ray onsets are bracketed respectively in ((2278381.710,2278381.712)), ((2278382.112,2278382.114)), ((912559.997,912559.998)). More exactly they are the unique roots between the stated endpoints of, respectively,
[
 t^3(e^{q-gamma}/t-1)=.2,qquad t^3(u-M-log t)=.2,qquad
 t^2(v+B_3-t)=.3,
]
where (q=log Q(2278381)), (u=sum_{ple2278382}1/p), and (v=sum_{ple912559}(log p)/p). These are onsets for inequalities with (le); at the exact root equality holds. There is no prime jump between the bracket endpoints (each bracket is interior to a single integer unit interval). The normalized positive errors decrease strictly in those brackets; the signs and derivatives below justify extension from the new root up to the certified outward endpoint. Witnesses on the other side preclude an earlier whole ray. Thus these baseline coefficients cannot be reduced at arbitrary earlier onsets. The tabulated outputs improve **strictly** on the entire respective baseline rays and include a short real extension at baseline strengths. The analytic proof below also gives error functions smaller than these coefficients for many (x), notably in the range (50le tle2100).

**Contract-powered candidate.** For every real (xge e^{200}), define
[
egin{split}
 V(t)&=1.05e^{-t/2}+.75e^{-2t/3}+10e^{-3t/4},\
 H_A(t)&=rac{e^{-kappa t}}{64}
        left((1+1/kappa)t^2+2t/kappa^2+2/kappa^3
ight),\
 K_A(t)&=rac{e^{-kappa t}}{64}
        left(t+(t+1)/kappa+1/kappa^2
ight),qquad kappa=5/32 .
end{split}
]
One has ( -H_Ale Jle H_A+V), ( -K_Ale Ule K_A+V/t), and
[
  -K_Alelog L_Q=-log L_Ple K_A+V/t.
]
In particular the two relative errors together are bounded by (exp(K_A+V/t)-1), with sharper individual one-sided bounds obtained by exponentiating the displayed interval (e.g. (e^{-(K_A+V/t)}-1le L_P-1le e^{K_A}-1)). For all (tge200) these envelopes are (<.001/t^3) for products and unweighted reciprocals, and (<.001/t^2) for the weighted sum. They are power-saving, not merely new constants of the same shape. Take their minimum with the noncontract estimates anywhere both apply. An optional offset bound replaces (V/t) by the actual prime-power spill or its approximation, below.

**QRH-powered candidate.** Without PsiMajorant, for every real (xge e^{258}) the same statements hold with (H_A,K_A) replaced by (d_Q+I_Q, d_Q/t+(t+1)I_Q/t^2), respectively (qrh.md). They satisfy the same (0.001) scaled comparison on that ray. No QRH input is used by the table or the contract formulas. Candidates are separate for their assumptions; multiple outputs in one row are correlated.

## Identities and prime-power spill

Let (D(s)=e^{-s}psi(e^s)-1), (H(t)=sum_{nle e^t}Lambda(n)/n-t+gamma), and (K(t)=sum_{nle e^t}Lambda(n)/(nlog n)-log t-gamma), with sums starting at (n=2). Precisely,
[
 H(t)=D(t)-int_t^infty D(s),ds,qquad
 K(t)=D(t)/t-int_t^infty D(s)(s+1)/s^2,ds
     =H(t)/t-int_t^infty H(s)/s^2,ds. 	ag{1}
]
Use Abel partial summation (point terms at (e^t) kept, even if a prime power), then take the upper limit to infinity. Convergence of the integrals involving (D) follows even without contract or QRH, e.g. from FKS Corollary 1.4. The constants (H(infty)=K(infty)=0) follow respectively from Dusart 5.7 and 5.9 with the definitions and convergent positive prime-power sums. For (K), the difference between (log Q) and its von Mangoldt sum tends to zero by the spill estimate below. Thus constants are justified without any new tabulated Euler constants.

Write (T=sum_{kge2, p^k>x}(log p)/p^k), (T'=sum_{kge2, p^k>x}1/(kp^k)), (C_*=sum_{kge2, ple x<p^k}1/(kp^k)). Then (J=H+T, U=K+T', log L_Q=K+C_*), and (0le C_*le T'le T/t). These follow by separating the first powers, using the convergent series for (-log(1-1/p)), and subtracting the full higher-power constants. In particular the spill is **positive**, so it need not be added in the negative direction. The estimates for (tge200) now follow from the exact integrals of the two polynomial-exponential integrands in (1); no upper endpoint is excluded. All monomials in those majorants times the appropriate (t^2) or (t^3) decrease from 200 onward; the rational endpoint tests allow slack before comparing (exp(z)-1le z/(1-z)) for (0le z<1).

To prove (Tle V(t)) on (xge B=2^{28}), use the following generic inequality: if (ell yle	heta(y)le uy) on (yge z), then for (k>1),
[
 sum_{p>z}rac{log p}{p^k}
 le (u-ell+u/(k-1))z^{1-k}.
]
It comes from partial summation at (z) and integration. For squares take (z=sqrt x, (ell,u)=(.97,1.01)); these constants hold for (zge10^4) by CH2 Lemma 9.2 ((|psi-y|le.791sqrt y) on (10^4le yle10^{13})), CH2 Cor. 1.3 beyond that, and the Dusart prime-power correction. The coefficient is (1.05). For cubes take (z=x^{1/3}) and ((ell,u)=(.9,1.1)) from Dusart Thm. 4.2, (k=2,eta_2=3.965), since (3.965/(log B/3)^2<.1). The coefficient is (.75). For the remaining powers split primes at (z=x^{1/4}). For (ple z) the geometric tail is (le2(log p)/x), hence (le4z/x) summed. For (p>z) it is (le2(log p)/p^4), and (	heta(u)le2u) bounds the sum by (16/(3z^3)). The use of 10 is a rational rounding upward. In particular the corrections are uniform and not fitted to data.

## Whole-ray analytic portion of the table

The following details yield exact functions before scaling. Put (a=1.048cdot10^{-12}), (h(t)=a+113.67e^{-t/2}), (b=29.9, c=57), (D_+=.791, D_-=.751). Write
[
 C_H=h(c)+.04c^2 e^{-c/2},quad C_K=(h(c)+C_H)/c,quad
 H_0=C_H+.08(b^2+4b+8)e^{-b/2},quad K_0=C_K+.08(b+3)e^{-b/2}.
]
Use the signed CH2 Lemma 9.2 estimate (-D_-e^{-s/2}le D(s)le D_+e^{-s/2}) from (B) up to (e^b); (e^b<10^{13}). Use the finite RH paper's Corollary 1, PDF p. 4, for (|D(s)|le .04s^2e^{-s/2}) on ([b,c]). Finally (|H(s)|le h(s)) on the whole ray from CH2 Cor. 1.3. Mixing the two identities of (1) at (c), the finite-range forms are
[
 H(t)=D(t)-int_t^c D(s),ds+H(c)-D(c),quad
 K(t)=D(t)/t-int_t^c D(s)(s+1)/s^2,ds
       +[H(c)-D(c)]/c-int_c^infty H(s)/s^2,ds.
]
The absolute anchor contributions are bounded by (C_H,C_K). At (log Ble tle b) it follows that upper bounds for (H+T,K+T') are
[
 (D_++2D_-)e^{-t/2}+H_0+V(t),
 qquad (D_++2D_-(1+1/t))e^{-t/2}/t+K_0+V(t)/t.
]
Upper bounds for the negatives use (D_+,D_-) interchanged and drop (V,V/t). The very same bounds handle the products and both prime sums. At (ble tle50) the bounds in absolute value are respectively
[
 .04(3t^2+8t+16)e^{-t/2}+C_H+V(t),qquad
 .04(3t+6)e^{-t/2}+C_K+V(t)/t.
]
At (50le tle2100) use (h+V, 2a/t+113.67e^{-t/2}(1+2/t)/t+V/t) directly by (1). At (tge2100), FKS Corollary 1.4 gives (|D(t)|le250/t^4): check the endpoint and note the negative log derivative of (t^{11/2}e^{-.8476836sqrt t}). Then the corresponding bounds are
[
 250(t^{-4}+t^{-3}/3)+V(t),qquad
 250((6/5)t^{-5}+t^{-4}/4)+V(t)/t.
]
The rational interval mesh in mertens_tail.py certifies (t^2) or (t^3) times all these bounds (<.0899) for the stated ranges. On each mesh interval a decreasing term is evaluated at the lower endpoint and an increasing one at the upper endpoint. The long ranges from (t=50) use monotone terms, or a constant times the bounded increase of (t^2); hence the comparison is a whole-ray assertion. Exponentiation gives the strict .090 product coefficient. On overlapping domains all these pointwise analytic functions may be minimized with the tabulated and power-saving bounds.

## Finite certificate and its interpretation

Run `/usr/bin/python3.10 mertens_sieve.py` (ordinary integer interval arithmetic, no optimizations disabling asserts, no external prime tables). The script enumerates all primes through (B=2^{28}) by deleting odd multiples from (p^2); composite deletion follows from least prime factors. On prime-free open intervals the partial sums are constant. The maxima of the scaled error bounds occur at endpoints when the unscaled absolute difference is (<1/4): for positive errors (w=q-gamma-log t) or (u-M-log t), the derivative of (t^3w) is (t^2(3w-1)<0). For products use the surrogate (t^3(w+.501w^2)) for (|w|le .001); its positive-side derivative is (t^2(3(w+.501w^2)-(1+1.002w))<0). On negative errors the absolute values and the scaled envelopes are increasing. The series of the exponential gives (max(e^w-1,e^{-w}-1)=e^{|w|}-1le |w|+.501|w|^2) for (|w|le .001). For (w=v+B_3-t), the derivative of (t^2w) on the positive side is (t(2w-t)<0). At prime arguments the left and right sums are tested separately (with right inclusive), and nonprime cuts / specified onsets are included. The witness routine uses lower bounds rather than merely a floating-point sign.

All roundoff is outward integer arithmetic at scale (2^{64}). For logs write (x=2^k m), (1le m<2); tabulate the lower integer logs of (j/256), (256le j<512), and (log 2) independently by the atanh series in cert.py. Set (a_0=lfloor256m
floor/256, z=(m-a_0)/(m+a_0)), so (0le z<1/512). The three terms (2(z+z^3/3+z^5/5)) are rounded downward; the omitted tail is (<2z^7/(7(1-z^2))), less than one unit. For the integer code, loss in (z) is (<1) unit, loss in the scaled square is (<1+2/512), and rounding the cubic or fifth power successively loses (<1+1/100) unit each (multiply the propagated errors by the factor magnitudes, (z<1/512, z^2<1/512^2)). Dividing by 3 or 5 adds at most one unit per term. This proves the (k+12) log radius including the table uncertainty. For (log t) apply the same enclosure then use that ((log t)'=1/tle1) where tested. For (-log(1-1/p)) the code uses three terms at (pge65536), six at (1024le p<65536), with the tail bounded by (1/((m+1)p^m(p-1))) after (m) terms; in both cases it is (<1) unit. Small primes use rational log intervals. The other sums use simple divisions of those intervals.

For the constant enclosures no decimals from external tables are assumed. At (n=2^{19}), sum (1/j) with integer enclosure and use
[
 0le gamma-(H_n-log n-1/(2n))le 1/(6n^3)+1/(12n^2).
]
Indeed (H_n-log n-gamma) is the sum over (jge n) of (int_j^{j+1}du/u-1/(j+1)). Replace each integral by the trapezoid formula; the error is nonnegative and at most (1/(6j^3)) by the second derivative bound, giving the inequality by the integral comparison. For the prime constants let (delta=.00014); (|	heta(y)-y|ledelta y) on (yge B) by CH2 Lemma 9.2 + Cor. 1.3 and Dusart's prime-power correction, as checked in mertens_tail.py. With (g(y)=y^{-2}/log y), partial summation shows
[
 left|sum_{p>B}p^{-2}-int_B^infty g(y),dy
ight|
 le 3delta/(Blog B).
]
Use (int_B^infty g=B^{-1}int_0^infty e^{-v}/(log B+v),dv) and the odd / even finite geometric expansions through degrees 5 and 6 (they bound the integrand for all (vge0)). The (kge3) tail of the (1/(kp^k)) sum is (le1/(2 B^2)) by comparison with the integer geometric tails. For (g(y)=1/(y(y-1))), partial summation likewise bounds the log-weighted tail by (log(B/(B-1))pm3delta/(B-1)). These certify the proposed constant intervals after the sieve. Both constants are constrained at the end; successful point loops alone are insufficient.

## Sources and statuses

* Dusart2018 (DOI as in index), Theorems 5.6–5.7 (printed pp. 243–245, PDF pp. 17–19), Thm. 5.9 (printed pp. 245–246, PDF pp. 19–20); Thm. 4.2 and its proof (printed p. 237, PDF p. 11).
* CH2, Corollary 1.3 (PDF p. 3) and Lemma 9.2 (PDF p. 35), using the signed psi portions only of the latter; don't infer a missing normalization in the separately extracted (9.1). These are source-trust inputs, not rerun computations.
* PlattTrudgianFiniteRH, Corollary 1 (PDF p. 4); FKS Corollary 1.4 (section 1.2; explicit tail only). QRH sources given in qrh.md. INPUT_CONTRACT.json for the faster tail.
* The finite table and witnesses are new certificate computations. No source-first verification or formal kernel theorem is claimed. Run the analytic inequalities independently via `/usr/bin/python3.10 mertens_tail.py`. In conjunction with the proof this uses no unverified approximations as hypotheses.
