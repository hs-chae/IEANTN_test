# Mertens and prime sums: repaired coverage, separate products and wider power-saving rays

Let t=log x. P_raw and Q_raw count p<=x with the jump included. Set P*=e^gamma*t*P_raw, Q*=e^(-gamma)*Q_raw/t=1/P*. Write q=log Q*, u=sum_{p<=x}1/p -log t-M, and j=sum_{p<=x}log(p)/p -t+B3. The constants, exactly as in Dusart 2018 Thms 5.6 and 5.7 (PDF pp.17–19), are

    M = gamma + sum_p [log(1-1/p)+1/p],
    B3 = gamma + sum_p log(p)/(p(p-1)).

All numerical rows below are strict upper bounds, from and including the stated real onset (except explicitly described exact roots). In B0 no hypothetical assumption is needed.

## New constant rays, to be intersected with all other branches

The bounds are c*x^(-1/8)/t for |P*-1|, |Q*-1|, |u|, and c*x^(-1/8) for |j|.

| Onset | c |
|---|---:|
| x=420000 for products and unweighted sum; x=550000 for weighted sum | .01325 |
| t=200 | .01241 |
| t=250 | .01062 |
| t=300 | .00969 |
| t=1000 | .00742 |
| t=2300 | .00703 |
| t=50000 | .00669 |
| t=100000 | .00668 |

For comparison, D01's .019851 and .01985 held from t=200. At the respective first onsets the new power bound does not automatically beat every logarithmic result. Let f(t)=.01325*t^2*e^(-t/8). The late crossovers f(t)=.2 and f(t)=.3 are respectively in (35,36) and (28,29), by exact tests, strict decrease on t>16 and f(log 420000)>.3 with increase before t=16. Thus the pure-power row is weaker than the respective raw logarithmic tolerance until each crossover on the common domain, and strictly better afterward. Other pointwise candidates are retained even when they are better than both. The later rows change coefficients at fixed functional shape; the continuous spectral expression below permits limiting coefficients less than .006664+3.1e-12 (not an asymptotic equality for actual errors).

Here are additional common logarithmic rays: c/t^3 for products and |u|, c/t^2 for |j|.

| Onset | c |
|---|---:|
| x=2*10^8 | .051 |
| x=10^9 | .027 |
| x=10^10 | .0105 |
| t=34 | .00227 |
| t=36 | .00105 |
| t=38 | .00048 |
| t=40 | .00022 |
| t=42 | .000096 |
| t=45 | .0000282 |
| t=50 | .00000352 |
| t=55 | .000000422 |
| t=57 | .000000193 |
| t=60 | .000000075 |
| t=65 | .0000000400 |
| t=70 | .0000000370 |

For smaller x and the weaker no-QRH source subset keep the D02_mertens.md finite-plus-analytic table; its noncontract proof and its finite replay are independent of exponent 27/32. Also keep the D01_mertens.md intermediate whole-ray rows (replace H in the old tail by its B0 proof) and its signed bounds. No later-onset cap is extended backward without a proof.

## Separate P and Q onsets at the original tolerance

Sharp smallest closed real ray starts (non-strict tolerance):
* Joint products, or Q alone (.2/t^3): (2278381.710,2278381.712).
* P alone (.2/t^3): **(2278381.575,2278381.577)**.
* Prime reciprocals (.2/t^3): (2278382.112,2278382.114).
* Weighted prime reciprocals (.3/t^2): (912559.997,912559.998).

Bracket entries denote open brackets for exact roots, not the claimed smallest onsets themselves. Equality holds at the root; for strict tolerance the corresponding open ray holds, with no minimum closed onset. For Q, u, and j use the exact root definitions and bracket checks in D02_mertens.md and D02_mertens_sieve.py. For P let p=2278379, p_next=2278421 and A=exp(-gamma)*Q_raw(p). On the entire prime-free interval [p,p_next), Q*=A/t>1 and |P*-1|=1-t/A. Thus its exact root solves t^3(1-t/A)=.2. The derivative is negative there because 3A<4t at the left endpoint. The strict opposite signs certified by mertens_new.py use the current finite sieve stdout; this also proves earlier failure on an open neighborhood below the root. From this root until 2278382 use the same decreasing function within the prime-free interval; beyond 2278382 use the joint D02 cap .19998. In particular P alone satisfies stricter caps .199999 from 2278381.59, .19999 from 2278381.69 and .19998 from 2278381.81, with denominator t^3, all strict on closed rays. These are not shared by Q on all those onsets. Q drives the joint boundary. P and Q are not independent experiments.

## Analytic error intervals, with genuine pointwise selection

Write D(s)=e^(-s)*psi(e^s)-1 and define

    H(t)=sum_{n<=x} Lambda(n)/n -t+gamma,
    K(t)=sum_{n<=x} Lambda(n)/(n log n) -log t-gamma.
    H(t)=D(t)-int_t^infty D(s) ds,
    K(t)=D(t)/t-int_t^infty D(s)(s+1)/s^2 ds.

These are the exact Abel identities keeping endpoint atoms. The constants follow from Dusart Thms 5.7 and 5.9 and the absolutely convergent higher powers (the product split tends to zero); integrability even without QRH follows from FKS Cor.1.4. The actual prime-power spills are

    W=sum_{k>=2, p^k>x} log(p)/p^k,
    V=sum_{k>=2, p^k>x} 1/(kp^k),
    U=sum_{k>=2, p<=x<p^k} 1/(kp^k).
    j=H+W,   u=K+V,   q=K+U.

In particular 0<=U<=V<=W/t. The analytic point terms and tails need not pay the same psi error bound. If [-D_-(t),D_+(t)] encloses the point error D(t), a spectral bound for the integrated weighted error is

    J_b(t)=.0462 e^(-t/2)+3.1e-12 e^(-(1-b)t)+1.84 e^(-t).

Respective tail radii for H and K are J_b and (1/t+1/t^2) J_b. Proof: for a>=0 insert the classical formula Dusart (2.1), PDF pp.3–4, into S_a(x)=int_x^infty (psi(y)-y)y^(-2-a)dy. A zero gives -x^(rho-1-a)/(rho(1+a-rho)); the constant and trivial-zero corrections together have magnitude <1.84 in the original integrand for y>=100. Absolute integration of the zero terms is justified by the L^2 compact-interval argument and absolute convergence after integration detailed in D01_mertens.md. Explicitly a dyadic ordinate block has O(T log T) zeros with O(log T) per unit interval by FKS Lemma 2.1/Rosser; the sum of the pair inner product upper bounds for a given zero is O(log^2 T). With coefficients 1/rho this gives squared L^2 norm O(log^3 T/T), summable in norm over dyadic blocks. Then integrate against the bounded kernel on compact intervals and pass to infinity using the strip/absolute integrated convergence. For the low zeros on the line use the positive-real-part identity sum 1/[rho(1-rho)]=2+gamma-log(4*pi)<.0462 (CH2 (B.9), PDF p.46; derivation in D01_mertens.md). For the high zeros use 2 times CH2 Lemma B.5 at 3e12 (<3.1e-12), and |rho||1+a-rho|>=gamma_ordinate^2. Use the exact finite RH height if desired; this only reduces that latter estimate. The result is |S_a|<=x^(-a)J_b. Integrate against (1+a) da (Fubini allowed by absolute integrability in the arithmetic-tail kernel) to get the K radius, using int_0^infty (1+a)e^(-a*t) da=1/t+1/t^2. This cancellation saves the usual factor 1+1/(1-b) in the leading weighted-sum coefficient and the analogous loss for the logarithmic kernel.

Take the minimum with the **Abel integral** alternatives for either tail side, integrating the signed pointwise psi bounds; for the sign of the tail in H or K, the upper error uses the lower point error magnitude and vice versa. Include the original CH2 bound on H from Cor.1.3, and the D02_mertens.md analytic signed intervals where applicable (in particular the finite-RH anchor and its FKS tail, no QRH used). The exact positive-step and continuous psi profiles in power.md are used directly as point error bounds, or in the Abel integral options; their integral tails are absolutely convergent. Any more precise prior J in D01_mertens.md may also be used at its valid premise and domain.

For t>=log(5e6), use the proved spill bounds V_+,W_+ in D01_mertens.md, with 0<=U<=V<=V_+, 0<=W<=W_+. For x>=1e8, W_+<=1.092/sqrt(x). All constants and subdomains are from the old proof and its rechecked scalar script. The following optional signed centering sharpens the interval for each spill independently, with the old constraints still kept. For k=2,3 put y=x^(1/k), and for f(v)=v^(-k) or v^(-k)/log v use the center I_f(y)=int_y^infty f(v)dv. CH2 Cor.1.3 with the Dusart prime-power bound gives |theta(v)-v|<=a*v+B*sqrt(v) for v>=2, a=1.048e-12, B=115.1. Partial summation gives an exact radius for the difference between int_(y,infty) f dtheta and I_f(y), namely the upper bound
    2 f(y)(a*y+B*sqrt(y)) + int_y^infty f(v)[a+B/(2sqrt(v))]dv .
This follows by using the signed boundary at y and integrating (-f') against a*v+B*sqrt(v) by parts. The k-th contributions to W and V use these centers/radii (divide the logarithmic kernel by k). For U subtract the log-kernel counterpart at y=x, because p>x is excluded; interval subtraction gives a valid enclosure. For k>=4 use [0,3.37*x^(-3/4)] for the remaining weighted spill and that upper bound divided by t for the others, from the split at x^(1/4) in D01_mertens.md. Intersect with zero and with old spill intervals, including finite sign and lower-spill bounds where proved. This yields sharper sign-sensitive transfers without claiming an actual sign in the remote tail.

Given intervals for D, a tail and a spill, add endpoints, retaining each on its specified domain. At the end intersect all valid signed intervals for q,u,j. For q in [l,u0], the relative intervals are exactly enclosed by [e^l-1,e^u0-1] for Q and [e^(-u0)-1,e^(-l)-1] for P. Also intersect with every theorem-level relative error cap and finite cap before extracting absolute bounds. For instance the signed finite q>0 gives |P*-1|= (Q*-1)/Q*, so finite caps can be tightened for P separately. For 2<=x<=1e8 an optional pointwise branch is to evaluate the dyadic arithmetic intervals for the constant values on [p,p_next) in sieve_repaired.c, with the same certified G,M,C3 intervals generated by that code; subtract the actual log log x or log x interval and exponentiate the respective ends. This defines an envelope at every real x in its domain, including both one-sided limits, not an interpolation between sampled errors. For x at a prime use the after-jump arithmetic sums.

## Proof of the simple rays and finite joins

For the pure-power table divide by the coefficient scale: bound e^((1-b)t)|j| and t*e^((1-b)t) times the logarithmic and reciprocal deviations. On t>=186 use C_b(t) from power.md plus
    (1+1/t)*e^((1-b)t)J_b(t) + 1.092 e^(-(b-1/2)t).
This normalized sum is decreasing on the full ray (constant positive high term, decaying other terms). For the last rows use the continuous bound d(b)*t/(t-140) plus the two remainders and the same J/spill. For 1e13<=x<=e^186 use a+Bpsi/sqrt(x), Bpsi=113.67, for |D|; here the normalized formula is a sum of positive exponentials and a constant after freezing 1+1/t at the left endpoint. It is convex, so checking both ends suffices. On [1e8,1e13] the signed CH2 input and the spectral plus spill bound give at most 1.94 exp(-(b-1/2)t) in the normalized scales (D01_mertens.md and check_mertens). On [550000,1e8] use the repaired finite auxiliary cap 1.88 in sqrt-scale. For the two unweighted log errors the 1.70 cap on [420000,1e8] suffices for the earlier onset, as verified separately. Each cap is converted with e^v-1<=v/(1-v), with positive denominator (checked); when a positive scaled cap A holds on t>=t0, bound the scaled relative errors by A/(1-A*e^(-(1-b)t0)/t0). Each part includes its joins, so this proves an entire real ray even across the CH2 plateau.

For the logarithmic table through 1e13 use 1.94*t^2*exp(-t/2) (decreasing on these ranges). From 1e13 through e^57 use finite RH Cor.1 (PDF p.4), |D|<=.04*t^2*e^(-t/2), with .04>1/(8*pi) and e^57<2.169e25. After multiplying by t^2 the term .04*t^4*e^(-t/2) decreases. At e^57 through e^186 use the CH2 plateau, replaced by its worst a*186^2 in scaled coordinates; other terms still decrease, and from 186 use the pure-power expression times t^2*exp(-t/8), decreasing there. The joins and exponentiation are tested explicitly by mertens_new.py at all the anchors. This is an analytic entire-ray deduction, not a sample extrapolation.

## Finite repair and original comparator

The original D01 sieve only executed the auxiliary upper checks when p>=10000. The enclosing prime gap was [9973,10007), so the historical receipt did not cover [10000,10007). sieve_repaired.c checks the upper bound whenever q>10000 and substitutes log(10000) and log log(10000) for the left smooth subtractions if p<10000. The partial sums are still those at p=9973. The positive multiplying bounds are still computed using q. The lower sign checks and unrelated main tables are unchanged. Fresh stdout explicitly prints the clipped cell and both endpoint anchors; the new P checks consume it. The fixed-point and prime sieve correctness arguments in D01_mertens.md still apply, with signed 128-bit products checked, and the replay also passed the undefined-behavior-sanitized build. This is not source-first verification.

The traditional comparators include Dusart 5.6 (x>=2278383), 5.7 (x>=912560), and 5.9 (x>=2278382), non-strict O* tolerances. Also retain their proof envelopes (§5.3–5.4, all applicable Theorem 4.2 rows with convergent integrals): for a theta bound eta*x/t^k on its given ray, the |u| cap is eta/(k*t^k)+eta*(1+1/(k+1))/t^(k+1), and for k>1 the |j| cap is eta/( (k-1)*t^(k-1))+eta/t^k. The general version replaces monomials by the actual available theta error and its positive-kernel tail. Products can be reconstructed from q=u-C_tail where 0<=C_tail=sum_{p>x,k>=2}1/(kp^k)<=1/(2*floor x) by integer telescoping (or use the stronger quoted original bound in the proof of 5.9). All valid original CH2 Cor.1.2–1.3/Lemma 9.2, finite RH Cor.1, Dusart 4.2–4.5, Platt–Trudgian 2021 Theorem 1/Cor.1, FKS Theorems 1.1–1.2/Tables 5–6 and Cor.1.4 error majorants can be minimized on their correct domains in these kernels; no finite error cap is extrapolated beyond its upper end. The signed power transfers and the floor of historical certificates are also retained in the submitted comparison. The strongest lawful comparison in the logical sense is exact: since B0 entails H, adjoining H cannot strengthen any valid B0 conclusion. The pointwise reporting rule is to take the best available bound without discarding any of the above originals, not to claim that this particular calculated atlas exhausts all possible B0 proofs.

The earlier tangent density integration, use of the raw H term, and the unsmoothed Abel triangle tail all give larger radii in the decisive ranges. Improving the power exponent or a universally better logarithmic factor at infinity is not established: QRH permits equality at the boundary, and the point term D(t), not the integrated tail or prime-power spill, controls the leading radius. Attempts and exact failed numerical targets are tracked in replay.md.
