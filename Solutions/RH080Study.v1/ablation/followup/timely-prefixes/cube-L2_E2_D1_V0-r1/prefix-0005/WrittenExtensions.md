# Written extensions: two distinct assumption packages

These arguments are written derivations, not a report of sampled primes. Their exact scalar checks are in `scalars.py`. Unless separately identified in the build log, the written proof itself is not a Lean proof or an independently reviewed (tier E) proof. All logarithms are natural. In both results the count is strict-open and n is real.

## 1. Same original source package: 0.7803 on the full matched ray

Assume the inherited octic family, with exactly its original RH + Green + Nicolas + BPT source package. For every n≥exp(8),
`N(n³,(n+1)³) > 0.7803 n²/log n`.
No Schoenfeld or Büthe is used in this argument.

Put a=n³, b=(n+1)³, D=b−a, L=log n, and f(u)=√u log u. Let R=D/f(a) and k=ceil(R/16), a positive integer. Cut the entire interval (a,b) into k equal *open* cells of width H=D/k, with left endpoints u_i=a+iH for 0≤i<k. Put C_i=H/f(u_i); then the exact right endpoint of cell i is u_i+C_i f(u_i), not an approximate endpoint. The cells discard their shared boundaries, so their counts can be added as lower bounds for the whole open window.

Since f is positive and increasing on [a,b], C_i≤R/k≤16. Also R≥√n/L, and f(b)≤1.001 f(a). Indeed n≥2980, log(n+1)≤L+1/n, and (n+1)√(n+1)≤(n+2)√n (square both sides; the difference of squares is n²+n−1). The required product bound is (1+2/2980)(1+1/(8·2980))<1.001. The function exp(L/2)/L is increasing for L≥8.

In each of the following cases C_i≥1.03, and B_i=(8/9)−(0.91015−4.2/log u_i)/C_i exceeds 0.7803.
- If k=1 and L≤8.25, u_0=a and C_0=R≥6.82. Use log u_0≤24.75.
- If k=1 and L>8.25, then C_0≥7.49. Here L<12 because R≤16 while exp(6)/12>32; use log u_0≤36.
- If k=2, then 16<R≤32, so C_i>8/1.001. Also L<12, so log u_i≤3(L+1/n)<37.
- If k≥3, then R>16(k−1), so C_i>(32/3)/1.001. Discard the positive 4.2/log u_i term.

The four rational comparisons, and the endpoint values for the exponential bounds, are checked in `scalars.py`. When bounding (0.91015−4.2/log u_i)/C_i, each chosen upper bound for the numerator is positive, so division by the lower bound for C_i is safe.

Apply the inherited strict family in each cell. It gives N_i>B_i C_i√u_i=B_i H/log u_i≥0.7803 H/log b. Add the k strict inequalities. The result is N(a,b)>0.7803 D/log b. Finally D=3n²+3n+1 and
`(n²/L) log b ≤ 3n²+3n/L < D` for L≥8. No floor loss or unfilled tail occurs.

## 2. Smoothed hybrid: 0.98010 for every real n≥1013

Assumptions: ordinary RH, the **same general** Green, Nicolas and BPT predicates used by the octic baseline, **plus** the allowed Büthe (1.6)–(1.7) predicate on its finite range. No Schoenfeld is used. The conclusion is
`N(n³,(n+1)³) > 0.98010 n²/log n`.
This is a different (enriched) package from §1 and is not a proof in Mathlib from RH alone. The improvement over the direct Chebyshev hybrid is by local smoothing at the late crossover, not changing the Fourier penalty in any gap theorem.

### Finite limb

For 1013≤n≤m=2154433, (n+1)³≤10^19, n³≥1423, and the exact scalar `(1−0.98010)^2·1013>(19/30)^2` holds. Thus apply the Büthe-only consumer `CubeTheta.buthe_fixed`: the stronger coefficient 1−19/(30√n) is valid across this limb.

### Analytic limb: application of the original Green hypothesis

For n≥m, let a=n³, b=(n+1)³, g=√(ab), t=log n and d=(1/2)log(b/a)=(3/2)log(1+1/n). Set A=0.997d and B=0.003d. Consider the real even trapezoid
`F(s) = (1_{[-A,A]} * (1_{[-B,B]}/(2B)))(s)`.
It is continuous, 0≤F≤1, supported on [−d,d], zero at its extreme endpoints, and has integral 2A. For an even smooth nonnegative unit-mass bump supported on [−ε,ε], use its convolution F_ε with F and let ε→0+. This converges uniformly to F, has the same mass, and the Fourier multiplier has modulus ≤1. The weight in the physical prime variable is `w_ε(y)=y^{−1/2} F_ε(log(y/g))` for y>0 and zero otherwise. In the Green predicate choose X=2 and W(v)=w_ε(2v). For sufficiently small ε, the support of w_ε lies in [a/2,2b] with a/2>2; W is smooth, compactly supported, and supported in [1,∞). Thus the stated smooth Green hypothesis applies, not an unsmoothed extension assumed as a premise.

After change of variables the pole contributes `∫ y^{1/2} F_ε(log(y/g)) dy/y`. In the limit it is at least 2A√a. Under RH a nontrivial zero 1/2+iγ has Mellin factor `g^{iγ}∫ F_ε(s)e^{iγs}ds`, times its multiplicity. Conjugate zeros have equal multiplicity, and the γ=0 multiplicity contributes zero: this is exactly the inherited Nicolas+RH result `RHOcticPush.ZeroPairing.order_zero_on_real_axis`. The ordinary RH nontrivial/trivial decomposition and trivial multiplicity one are those of `OcticZeroDecomposition.lean`. Trivial zeros in total contribute at most
`∫ F_ε(s) y^{−5/2}/(1−y^{−2}) ds < 10^(−6)`
for y=g exp(s)≥a/2>10^18 and 2A<1. The main term and the finite arithmetic sum pass to the limit by uniform convergence and a fixed compact support; in the arithmetic limit w is zero at both endpoints, even if an endpoint is prime. The following absolute zero bound is uniform for the mollifiers; the use of a uniform bound in the inequality does not require a new equality at the nonsmooth weight.

### Analytic limb: bounding the absolute zero sum including two notches

The transform of F at γ (in the displayed Mellin convention) is
`2 sin(Aγ)/γ · sin(Bγ)/(Bγ)`, with continuous extension at zero. Let T0=1/A, T1=1/B, x0=2π, and define
`h(T)=A` for T≤T0, `1/T` for T0≤T≤T1, and `1/(B T²)` for T≥T1.
For positive ordinates the modulus is at most 2h(T), and the same after mollification. Both signs give the budget 4∫h dN_+, where N_+ counts *positive* ordinates closed at T with multiplicity. The baseline BPT endpoint adapter gives |R(T)|≤0.28 log T for T≥x0, where
`M(T)=T/(2π)·log(T/(2πe))+7/8`, `R=N_+−M`.
At x0, M(x0)=−1/8, so N_+(x0)=0 by the bound and integer-valuedness. Taking finite Stieltjes sums and integrating by parts on [x0,V], the boundary at V tends to zero since h(V)R(V)=O(log V/V²). The lower boundary is −h(x0)R(x0)≤0. The remainder in the two-sign budget is at most
`4·0.28∫_{x0}^∞(−h'(T)) log T dT = 4·0.28 (A log T0 + A - B/2)`.
The equality follows from integration by parts plus the three elementary integrals of h(T)/T. Since A≤1.5/n, A≥1/n, it is ≤1.68(t+2)/n.

Integrate the density M′=log(T/(2π))/(2π) against 4h. With l=log(T0/(2π)) and j=log(T1/T0)=log(997/3), the main integral is
`(2/π) [(2+j)l + j + j²/2 + 2πA]`.
To see the endpoint constants, the three integrals before multiplication by 2/π are l−1+2πA, lj+j²/2, and l+j+1. The geometry and exact scalar inequalities give 0≤l≤t−2.239, l≥t−2.25, j<5.81, and 2πA<0.00001. In detail, `1/(n+1)≤log(1+1/n)≤1/n`; combine this with the fixed rational bounds for π and exp in `scalars.py`.

To improve on the full envelope, use two disjoint bands (u/A,v/A] with triples (u,v,U)=(2.5,3.5,.60) and (5.5,7,.71). On either band h=1/T because 1<u<v<997/3. There |sin(AT)|≤U, so the budget at each zero in the band can be reduced by at least 4(1−U)A/v per positive zero (the factor 4 includes the negative ordinate). For the sine bound, reduce modulo π or 2π, so the absolute arguments are at most .642 and .785 respectively. For 0≤x≤these endpoints, sin x is nonnegative and increasing; `sin x≤x−x³/6+x⁵/120` by the alternating Taylor series. Checking at the endpoints gives the stated U. The lower bound for the positive count in each band is
`((v−u)/(2πA))(l+log u) − .28(log(u/A)+log(v/A))`
by integrating the increasing M′ and using the two BPT endpoint bounds. This is valid at zero ordinates (closed count difference). The combined gain is at least
`k1(t−1.35)+k2(t−.55) − 1.5(t+2)/n`,
where `k1=.636·.4/3.5` and `k2=.636·.29·1.5/7`. For the errors use log(u/A),log(v/A)≤t+2, A≤1.5/n, and `8·.28·(.4/3.5+.29/7)<1`. The gain argument is uniform in ε: the additional convolution multiplier never increases the modulus. The gain is applied to a **lower bound on the number of zeros**, not to a presumed sampling distribution of ordinates.

### Analytic limb: prime powers and conclusion

For k≥2 the number of integer kth roots in the cube interval is at most (n+1)^(3/k)−n^(3/k)+1, without even requiring that the roots be prime. For k=2 this is ≤2√n+1 by the mean-value theorem; for k≥3 it is ≤2. The exponent cutoff is k≤log b/log 2≤6(t+1), using log 2>.6. Thus fewer than 3√n root candidates, because `t+2 ≤ √n/50` across the ray. To prove the latter, write t=log m+v, v≥0, and use `√n=√m exp(v/2) ≥ √m(1+v/2)` with `(14.58304+2)/1467.798<1/50`. Each prime power contributes at most log b/√a≤3(t+1)/(n√n). Their total cost is ≤9(t+1)/n.

Together, the BPT remainder, notch-count errors, trivial zeros and prime powers cost <.001, since `(1.68+1.5+9)/(50√m)+10^(−6)<.001`. By the explicit main integral and the two notch gains, the entire zero plus prime-power cost is at most `4.864 t + 3.45`; the coefficient and constant are checked by rational arithmetic in the script. The prime-weighted sum is at most N(a,b)log b/√a, so
`N(a,b) ≥ [2A√a−4.864t−3.45]√a/log b`.
This bracket is positive by the next uniform scalar estimate. Normalize by n²/t: using 2A√a≥0.997·3√n·n/(n+1), the normalized right side is at least
`[.997(1−1/n)−(4.864t+3.45)/(3√n)] · (1−1/(nt))`.
The loss term (4.864t+3.45)exp(−t/2) decreases for t≥14 (differentiate), and t≥14 for n≥m. Therefore the expression is bounded from below by substituting m and T=14.58304, replacing √m by its lower rational bound 1467.798, and replacing t in the last factor by 14. This positive exact rational lower bound is > .98010. This completes the late limb, and together with the finite limb proves the stated written result.

## Checks and audit boundaries

`/usr/bin/python3.10 /work/submission/scalars.py` checks rational constants, using a finite Taylor sum for exp and a geometric bound on its positive tail. No sample of primes or zeros is used for these universal estimates. Its π bounds are the standard Mathlib `Real.pi_gt_d6` and `Real.pi_lt_d6` (weakened to 3.142 there). The main analytic identities and inequalities in this file are written derivations; the Python assertions alone do not certify any theorem. The source interfaces/locators are Green, *The Prime Number Theorem*, Def. 7.1 and Thm. 7.1, printed p.40 (baseline `OcticGreenSource.lean`); BPT, *Sharper bounds for the error term in the prime number theorem*, JNT 238 (2022), Cor. 1, p.743 (baseline `BPTZeroCount.lean` and `OcticBPTSourceEndpoint.lean`); and Nicolas (1.19) exactly as in the inherited source predicate `NicolasContinuation.SourceNicolas119`, entering the late derivation via the real-axis multiplicity lemma in `OcticZeroPairing.lean`. No new C/C++/CUDA source verification or gap statement is involved.

## 3. Denser rigorous notch certificate: 0.9848 from real n≥1737

The assumption package and analytic application are the same as §2. Replace the two hand-selected notches by the following finite rational certificate; nothing about actual ordinate locations is sampled. The proof of the remaining error terms and the finite Büthe limb are unchanged except for the new scalar coefficient/onset `(1−.9848)^2·1737>(19/30)^2`.

Set r=B/A=3/997. For each interval [u,v]=[i/10,(i+1)/10], i=1,...,11999, compute factors U and V bounding |sin x|/min(1,x) on [u,v] and [ru,rv]. They are each ≤1. For any such interval [a,b] with b≤1, use the alternating Taylor majorant 1−a²/6+a⁴/120, decreasing on [0,1]. Otherwise choose any integer k and use the maximum of |x−kπ| over endpoints x∈{a,b} and rational π bounds 3.141592,3.141593. If the resulting rational D is <3.141592/2, monotonicity of sin on [0,π/2] and the degree-five Taylor upper bound give min(1,(D−D³/6+D⁵/120)/min(1,a)). Otherwise use 1. The exact midpoint-based choice of k in the script only improves the bound; it is not needed for validity.

The quantity `w=(1−UV) min(1,1/v) min(1,1/(rv))` is nonnegative. On (u/A,v/A], the reduction in the two-sign budget is at least 4Aw per positive ordinate. By the same BPT argument as in §2 it is therefore at least
`(2/π)w(v−u)(l+log u)−1.12Aw(log(u/A)+log(v/A))`.
The bands are disjoint, with their left endpoints excluded. For log u use a dyadic decomposition u=2^k w0 where 1≤w0<2, the proper lower bound on k log 2 for its sign, and log w0≥2(w0−1)/(w0+1) by differentiation. The resulting l+log u lower bound is positive throughout this grid since t≥14, l≥t−2.25 and u≥.1 (even the rational log lower bounds suffice). Thus replace 2/π by .636. Sum the slopes and intercepts, rounding each toward −∞ to denominator 10^12, and write the resulting lower main gain as αt+β. For the endpoints use u/A,v/A≤n exp(8), A≤1.5/n; the total remainder is bounded by 3.36 S(t+8)/n, where S is the sum of 10^−12-rounded-up weights. In particular this error is ≤3.36S/(50√m), since t+8≤√n/50 by the same argument as in §2.

The analytic loss bound is therefore Ct+D+E, with
`C=.637(2+5.81)−α`,
`D=.637(5.81+5.81²/2+.00001−(2+5.81)·2.239)−β`,
and `E=(1.68+3.36S+9)/(50·1467.798)+10^−6`.
The exponential-normalized loss (Ct+D+E)exp(−t/2) decreases for t≥14 because C>0 and 12C+D+E>0 (both rational checks). Substitute the same m,T,√m lower bound as in §2 to obtain
`[.997(1−1/m)−(CT+D+E)/(3·1467.798)](1−1/(14m)) > .9848`.
All sums, rational interval operations, and comparisons are reproduced by `/usr/bin/python3.10 /work/submission/notches.py`. This completes the improved written all-real result. This is not a Lean formalization of the main analytic proof, nor source-first PV.
