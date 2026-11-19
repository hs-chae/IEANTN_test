# Ramanujan: strict profiles on connected real rays

Let h=x²/(log x)^6 and R=e*x*pi(x/e)/log x−pi(x)² using right-continuous counts, and write t=log x. A row (t0,k,w) means, strictly for **every real t>=t0**,
[
 R/h > \sum_{j=4}^{k-1} d_j/t^{j-4}+w/t^{k-4},\qquad
 d_j=\sum_{i=0}^j i!\binom ji-\sum_{i=0}^j i!(j-i)!.
]
The first coefficients are 1,14,145,1412,13985,145450,1610021,19063832,241691425,3277187246 (indices 4 through 13). Keep the pointwise maximum of all lawful rows, adaptive expressions and source branches, including those in ram-new.md, D01_ramanujan.md, and D02_ramanujan.md with their exact hypotheses.

## The true strict positivity onset is already attained in B0

The certified real root r is in (38358837682.217926,38358837682.217927); the strict ray is exactly x>r in the sense of the least left endpoint of an open sufficient ray. R(r)=0, with failure immediately to its left; no D02 improvement of this endpoint is possible. The local linear margin R(x)>67623427(x−r) holds on (r,38358837683]. The least integer sufficient onset is 38358837683. Proof and exact evidence: ram-new.md and D01_pi_exact.py / D02_count.py. In the later finite region use the integer-only restriction of Platt–Trudgian 2021 Theorem 2 (PDF p.3, proof §5), extending monotonically within integer cells and overlapping its endpoint exp(58) with the analytic rays here. Its literal real left endpoint is false, and is not used. Their original fixed closed exp(3915) ray and Dudek–Platt Thm 1.2's weaker exp(9658) closed ray remain valid; Dudek–Platt Thm 1.3 assumes **full RH** and is not credited to B0 or D02. Without QRH and without D02 keep the disconnected optional result in ram-new.md; this work does not close its middle window.

## New B0 rows and stronger D02 rows

B0 (input-independent improvements, including earlier quantitative onsets):

| k | pairs (t0,w) |
|---:|:---|
| 4 | (36.57,.002), (36.61,.02), (36.7,.06), (36.88,.14), (37,.20), (38,.56), (40.01,1) |
| 5 | (45,10.2), (47.08,14) |
| 6 | (47.55,20.5), (49.5,24), (50,23), (170,23), (200,115), (217,145) |

B0+D02 (in addition to B0 and the applicable prior sensitivity rows):

| k | pairs (t0,w) |
|---:|:---|
| 6 | (48,48), (48.75,76), (49,82), (49.03,85), (49.2,86), (50,86), (172,108), (176,126), (185.4,145) |
| 7 | (189,535), (209.8,1412) |
| 8 | (235.1,13985) |
| 9 | (262,145450) |
| 10 | (292,1610021) |
| 11 | (319,19063832) |
| 12 | (348,241691425) |
| 13 | (378,3277187246) |

Redundant rows are shown when they record matched comparisons. At log-onset 50, the new common transfer certifies 86 instead of the B0 row 24 or the previous D02 sensitivity 82.4. At fixed coefficient 86 it already holds at 49.2. At coefficient 145, 185.4 instead of the new B0 217 or own prior conditional 186.6; at 1412 beyond that prefix, 209.8 instead of B0 253 or previous conditional 212. In the reconstructed common transfer at t=185 the B0 normalized degree-6 lower expression is <27 and its D02 counterpart >144 (compare_d02.py). This is a comparison of certificates, **not an upper bound on actual R**. The gain on rays beginning below t=80 is from refining the later interval of the ray, not evaluating the input below exp(200).

Here are matched new higher-order rows with w=d_k (exact integers defined above, also printed by the checker); the whole lower profile through k is retained.

| k | B0 t0 | B0+D02 t0 |
|---:|---:|---:|
|14|530|406|
|15|565|445|
|16|606|476|
|17|648|511|
|18|682|536|
|19|718|567|
|20|755|596|
|21|794|626|
|22|832|655|
|23|870|685|
|24|908|715|
|25|950|748|
|26|1010|778|
|27|1030|807|
|28|1070|838|
|29|1110|870|
|30|1150|902|
|31|1200|936|
|32|1240|968|
|33|1285|1002|
|34|1330|1035|
|35|1380|1070|
|36|1425|1105|

No claim of optimal numeric thresholds is made for these margins. The B0 portfolio is a reconstruction from permitted originals, not an independent blind run.

## Proof of the count transfer, including the oscillatory carry

For z=log y, the exact count identity (ram-new.md) normalizes pi(y)−li₂(y), li₂(y)=integral_2^y du/log u, by z/y. The point term is (theta(y)−y)/y. Use the upper and lower theta adjustments −.9999 and +1.4262 in square-root scale at z>=24 (Dusart Prop.4.3 and Thm 4.2 proof). For the signed point term use the smallest certified radius among CH2's heights in ram-new.md, CH2 Cor.1.3, theory_d02.md and the inherited signs. No sign hypothesis for the forward integral is needed.

Define A(s)=S_0^*(exp s), so A'(s)=−D(s) a.e. For z>=24 integrate the psi part of the count identity on [16,z] by parts:
[
 \int_{16}^z e^s D(s)/s^2\,ds
  =[-e^s A(s)/s^2]_{16}^z+
  \int_{16}^z A(s)(1-2/s)e^s/s^2\,ds.
]
Use the inherited J_b for A in this identity. For weight e^(-r s), r=.5 or 1−b, bound the integral by e^((1−r)z)/z² divided by 1−r−1/8, by differentiating the latter exponential-over-power at s>=16. For r=1 bound the integral by 1/16, and include that term in the prefix. The theta–psi correction above 16 costs 1.4262 times the square-root integral (8/3 multiplier). The lower boundary at 16, integral up to 16, initial 2/log 2, and the constant from r=1 are collectively <12000 before normalization: use CH2 Cor.1.3, the same 100000 and 100 integral checks in D01_check.py, and the direct exact test in gap_d02.verify(). Thus carry(t,b) in gap_d02.py is a symmetric upper bound on the normalized integral plus initial term, independent of which point radius was selected. As before we may intersect with r_T, inherited r_b and the permitted finite pi sign. In the new narrow-strip branch the tail factor e^(-(1−b)z) decreases faster; the coefficient (1+(1−(1−b)−1/8)^(-1)) has logarithmic derivative in 1−b <1, so that multiplied term decreases as the strip narrows at z>=24. The radical and prefix terms are unaffected.

In code, on z in [145,330) one can evaluate the new decreasing psi point bounds at an exact multiple of 1/32 no greater than the left edge of the cell; one choice of h from the finite list suffices throughout that cell. On boxes with left edge >=330 and <920 another option is C_b(330)e^(-(1−b)z). The shifted count uses z=t−1, and branch availability is checked at its own z. Elsewhere only safe inherited point bounds are used. The count radii and the exact inequalities define a pointwise adaptive profile even outside the checked rows; no particular choice of the minimum is required at a branch transition.

## li₂, the main polynomial, and entire-domain checks

Use P_N(z)=sum_{j=0}^N j!/z^j and C_N=4(N+1)!. For (N,v)=(14,24),(27,55),(37,75), the check at v proves P_N < z*e^(-z)*li₂(e^z) < P_N+C_N/z^(N+1). The convergent integral series is log(z/log 2)+sum_{j>=1}(z^j−(log 2)^j)/(j j!). At v the omitted tail after 4v terms is <2 v^(4v+1)/((4v+1)(4v+1)!) by ratios. Differentiate e^z P_N(z)/z: the deficit relative to e^z/z is (N+1)! e^z/z^(N+2). The derivative of the upper correction pays it because 4(1−(N+2)/z)>1 on the stated ray. Thus the anchor extrapolates to all real z>=v, including the shifted argument for the rows.

Expand (t/(t−1))*P_N(t−1) up to degree 2N in 1/t (omitted terms positive), and subtract the exact square P_N(t)². Call the difference coefficients D_j; they equal d_j for j<=N, and D_0 to D_3 vanish. Exact formulas are in Model.__init__. For applicable count radii u at t above and l at t−1 below, the loss in R/h is at most
[
 (2P_N+C_N/t^{N+1}+u)(C_N/t^{N-3}+t^4u)+t^5l/(t-1).
]
This follows from the square identity and the nonnegative upper prime count, and the linear shifted lower term. The strict inequality survives even if endpoint radii were non-strict, because the positive shifted series tail is omitted.

For finite boxes check the polynomial minus these losses and the row target, after multiplying by t^(k−4). The checker works with outward I-intervals (D01_check.py, scale 10^60), subdivisions cover both endpoints and either split or use a lawful fallback at transitions. On the infinite continuation, use the inherited radius r_b from ram-new.md and anchor at z=299: from that point e^((1−b)z) r_b(z) is nonincreasing, directly by its formula including the cutoffs. Hence set pref=e^((1−b)*299)r_b(299) and use pref*exp(−(1−b)z) thereafter. For a row with w<d_k the paying coefficient is d_k−w at j=k. With equality pay by the next positive coefficient d_(k+1) at j=k+1. Drop remaining positive coefficients while paying every negative term and the full loss on that scale. After multiplying by t^(j−4), each resulting upper cost decreases from the right anchor U: the powers in the losses are t^j and t^j*t/(t−1) against exp(−(1−b)t) or its shift, and U−1>=8(j+2). The positive square prefactor also decreases. Polynomial terms have strictly negative powers at n>j. The check pays all of them at U and consequently on the entire infinite tail. For Q at degree 26 and both columns at degree 27 onward this same test succeeds at the outset, so no finite certificate is needed. Arithmetic uses exp(j*log(t)−(1−b)t), not a vastly amplified rounding unit for exp(−(1−b)t).

### Limits and failed attempts

The target 87 at t0=50 did not certify near t=166.4, where the absolute errors at t and t−1 lie near the CH2-to-smoothing transition. The proposed d6 onset 185.25 fails for the actual lower expression used (its signed enclosure is below the target); similarly 215.5 for the new B0 process. Failing a certificate is not a negative witness for R. The B0 high-degree absolute-scale computation initially lost significance when multiplying rounded values of e^(-t) by t^j; the normalized analytic test repairs this without inventing precision. For the optional no-QRH gap the CH2 plateau cost remains ∼3*1.048e−12*t^4, already >3 at t=1000; saving the integral alone does not pay this. A two-point correlation proof would need more than the current cumulative ordinate bounds; an individual zero's two coefficients can add in absolute value for some phases of its shift, so a universal gain is not justified by simply replacing their sum by a Euclidean norm. The stronger strip does not change the factorial coefficients of either asymptotic expansion, and it cannot improve the already sharp real positivity onset.

