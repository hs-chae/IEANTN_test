# Further arithmetic consequences (new derivations)

These consequences use the density-powered bounds in density.md, whose input assumptions are retained exactly. They are not additional candidates for the two requested application families.

## Short intervals with many primes

Let (b=27/32) with PsiMajorant or (b=7/8) with the admitted QRH. Put ((t_0,C)=(200,.227)) in the first case, ((187,.014)) in the second. For every real (xge e^{t_0}), with (t=log x), there is a prime in
[
       (x,x+(2+10^{-10}) C_b(t)x^b],
]
where (C_b) is (D). In particular the simpler lengths (0.455,x^{27/32}) and (0.0281,x^{7/8}) respectively suffice. These replace the relative length (1/(5000t^2)) in Dusart Corollary 5.5 (printed p. 242, PDF p. 16) throughout these narrower domains. The new lengths times (t^2/x) decrease from the displayed onsets, and are respectively (<5cdot10^{-10}) and (<7cdot10^{-8}) at the onsets, compared with (0.0002). Thus the length is reduced by a factor exceeding (400000) and (2857), respectively, on the whole comparison rays (conditional/supplied-source assumptions as stated).

More generally put (E(x)=C_b(t)x^b), (t_2=t+log2), (f=t_2/sqrt x) and (g=t_2log(t_2/log2)). For (0le hle x),
[
 pi(x+h)-pi(x) ge rac{h(1-bE(x)/x-f)-2E(x)-g}{t_2}.
]
This lower bound can be rounded up to the next integer. To prove it, the decreasing (C_b) and concavity of (x^b) give (E(x+h)le E(x)(1+bh/x)). For any (mge2), the number of (m)th powers with integer bases in the interval is at most (1+h/(m x^{1-1/m})), by concavity of the (m)th root. Each prime-power weight is at most (t_2/m). Sum with (sum_{mge2}1/m^2le1) by telescoping and (sum_{2le mle t_2/log2}1/mlelog(t_2/log2)). This yields a uniform loss (fh+g) when transferring the (psi) difference to (	heta). Divide by the upper bound (t_2) on each first-power weight. This is much smaller than paying an entire (O(sqrt x)) penalty for the short interval.

At the stated onsets (bE(x)/x+f<10^{-12}), and these majorants decrease afterwards. Also (g/E(x)<10^{-12}): (C_b(t)ge c_0>.001) from the density formula and the rational enclosures; bound (gle 3t^2) using (tge187) and (log2>.69). The resulting ratio decreases, and is below (10^{-12}) at each onset. Insert (h=(2+10^{-10})E(x)), which is less than (x), to get a strictly positive lower bound. The certificates of these comparisons are in tertiary.py.

## Maximal totient ratio with cancellation of the endpoint error

Use PsiMajorant. For real (N) define
[
 {cal G}(N)=max_{1le nle N, ninmathbb{Z}} n/arphi(n).
]
Let (mathcal L=1+10^{-12}) and (Ngeexp(mathcal L e^{200})). Put (s=log(log N/mathcal L)), (d(s)=.227e^{-5s/32}), (u(s)=d(s)+1.4262e^{-s/2}). Then
[
oxed{displaystyle
 left|lograc{{cal G}(N)}{e^gammaloglog N}
ight|
 le
 rac{(1+1/s)d(s)}{(5/32)s}
 +rac{u(s)^2+1.4262e^{-s/2}+V(s)}{s}
 +2e^{-s}.}
]
Exponentiating gives a two-sided arithmetic estimate (and in particular an upper bound for (n/arphi(n)) with (N=n)). The removal of the endpoint term (d(s)/s) improves a direct triangle-bound estimate: among the first-order (d(s)) terms, the leading coefficient is reduced from (1+32/5) to (32/5) after factoring (d(s)/s), a reduction (5/37). This is an explicit magnitude estimate, **not** a sign assertion about the primorial error.

For the derivation, inclusion-exclusion over prime divisors gives (n/arphi(n)=prod_{pmid n}p/(p-1)). Comparing each divisor in the sorted list to the prime of the same index shows that among integers with (j) distinct prime factors, the first-(j) primorial has least size and greatest ratio. Thus (mathcal G(N)=Q(x)) for the last prime (x) in the largest primorial at most (N). The short-interval bound just proved gives a prime in ((e^{200},e^{200}+.455 e^{(27/32)200}]); for that prime (p), (	heta(p)le(1+u(200))p<mathcal L e^{200}). Hence (xge e^{200}). With (t=log x), the next prime (p'<2x), so (0lelog N-	heta(x)<log p'< t+log2). The same bounds imply (log N<mathcal L x), thus (tge s). By the mean value theorem the replacement of (loglog	heta(x)) by (logloglog N) costs (<2e^{-t}).

Let (y=	heta(x)/x-1), (D=psi(x)/x-1). Identity (1) in mertens.md gives exactly
[
 log Q(x)-gamma-loglog	heta(x)
 =-int_t^infty D(v)(v+1)/v^2,dv+C_*
   +(D-y)/t+{y/t-log(1+log(1+y)/t)},
]
where (D(v)) inside the integral denotes the function of the logarithmic variable there. The primary endpoint (D/t) cancels against the shift to the primorial normalization. Here (|y|le u(t)), (0le D-yle1.4262 e^{-t/2}), and (0le C_*le V(t)/t). The bracket's absolute value is bounded by (y^2/t): expand both logarithms with the elementary bound (|log(1+z)-z|le z^2/(2(1-|z|))), use (|y|<.01, tge200). The integral is bounded by (d(t)(1+1/t)/((5/32)t)) via (D) and the decreasing kernel. Each term of the resulting estimate decreases, so (s) can replace (t). All remaining numeric estimates are rational endpoint comparisons (tertiary.py).

## Optional explicit prime-square centering of Mertens estimates

For (t=log xge200) let (Delta(v)=a+115.1/sqrt v), a nonincreasing unconditional bound on (|	heta(v)-v|/v) for (vge1), from CH2 + Dusart in ramanujan.md. Let (I(z)=int_z^infty du/(u^2log u)), and (E(z)=3Delta(z)/(zlog z)), (zgesqrt x). By partial summation as in mertens.md, (left|sum_{p>z}p^{-2}-I(z)
ight|le E(z)). Similarly (left|sum_{p>sqrt x}log p/p^2-x^{-1/2}
ight|le3Delta(sqrt x)/sqrt x). The main corrections to the analytic parts of (J,U,log L_Q) can thus be explicitly centered at (x^{-1/2}, I(sqrt x)/2, (I(sqrt x)-I(x))/2), respectively. Their extra square errors are at most (3Delta(sqrt x)/sqrt x, E(sqrt x)/2, [E(sqrt x)+E(x)]/2). The remaining terms in each case are nonnegative and bounded by (.75e^{-2t/3}+10e^{-3t/4}) (divide by (t) for (U,log L_Q)). This both improves the left endpoint of the signed high-(x) estimates and allows tighter positive-side corrections when desired. It does not assert a sign for a product or prime sum.
