# Mertens: real-domain finite certificates and analytic tails

All branches here are B0. Keep all these bounds; for independent improvements and their pointwise intersection see mertens_postreview.md. All sums and products include p=x when prime. Use the centered quantities in candidate.md and Z_Q=log Q−γ−log L. Keep the validated D01 entire-domain and signed families (d01_mertens.md and d01_smooth.md). The envelope is the minimum of applicable absolute bounds, with signed intervals intersected where helpful before converting to the relative errors. Retain lawful source branches (comparison.md) and the supported D02 signed branches using δ=1/8 only.

## Earlier onsets, step improvements and repaired links

K(x) is the last eligible coefficient below. Both absolute relative product errors are ≤K(x)/L³; the same D1 bound holds **on x≥2278383**. Each row holds on the entire subsequent real ray, endpoints inclusive.

| Onset | K |
|---:|---:|
| 2278381.730 | .20000 |
| 2278381.940 | .19998 |
| 3500000 | .180 |
| 5000000 | .160 |
| 18100000 | .100 |
| 111000000 | .060 |
| 181000000 | .050 |
| 1125000000 | .030 |
| 3909288921 | .011 |
| 4760000000 | .010 |
| 8500000000 | .009 |
| 12000000000 | .008 |
| 16000000000 | .007 |
| 22000000000 | .006 |
| 30000000000 | .005 |
| exp(27) | .00205 |
| exp(32) | .001 |

For D2, the direct finite check gives .3/L² on [912559.998,2278383], .2999999/L² on [912560,2278383], and .29998/L² on [912561,2278383]. Each is a closed real interval. The .3/L² onset is .002 earlier than the original, and the constant improves strictly throughout the original domain. For x≥2278383 any D1 pointwise absolute envelope B(x) from this domain onward implies
`|D2(x)| ≤ L B(x)+∫_L^∞ B(exp v)dv.`
Indeed dD2=v dD1 in log coordinates; D2(exp v)−vD1(exp v)→0 by Dusart 5.6–5.7. Stieltjes integration by parts uses the inclusive value at x. In particular use 1.5K(x)/L² or integrate K(exp v)/v³ exactly across the step breakpoints. Splitting at L=27 gives for L≤27 the simpler \(L² |D2|≤1.5K−(K−.00205)(L/27)^2/2\); beyond 27 use \(1.5·.00205\) or stronger bounds. Directed calculations give whole-ray weighted coefficients .014 from 3909288921, .0124 from 4760000000, .0111 from 8500000000, .0099 from 12000000000, .0087 from 16000000000, .0075 from 22000000000 and .0064 from 30000000000, in units L^−2. These cones can intersect with the stronger pointwise transfer.

**Finite verification.** d02_mertens.md derives the finite prime-plateau algorithm and bounds γ, B3 and M. Products and D1 near 2278382 use d02_mexact.cpp. The weighted checks with seven decimal places in the coefficient use m_onset.cpp. The threshold functions log L ± k/L³ (D1), or L ± k/L² (D2), are increasing in the checked region, by differentiation. For products test a symmetric log error using the sufficient radius t−t²/2≤log(1+t), t=k/L³, whose associated thresholds are also increasing. Thus both one-sided endpoints of every plateau and the inclusive jump values are covered. [2278381.730,2278382] overlaps the .19998 range starting 2278381.940. The other early finite/analytic joins replay using the historical arguments; the D1 and D2 domains remain separate.

For .011 through .005 use m_coarse.cpp. At [a,b] lower-bound D1 using the prime reciprocal prefix at a (downward), subtract log log b and M upward; upper-bound using the opposite endpoints. Both inequalities hold across *all* intervening prime jumps. Subtract the tail upper bound 1/(2 floor(a)) for the lower Z_Q bound; the upper Z_Q bound needs no correction. The mesh endpoints a,b are integers. Reserve 999/1000 of the downward target t=k/(log b)^3: here t<.001, so (.999t)/(1−.999t)≤t covers both exponentials. Each rounding is directed at scale 2^60, including chained division in the target. The 40-term positive log series plus +300 units per block covers truncation plus arithmetic rounding (proof in d02_mertens.md). Use γ from harmonic n=10^6 and [2.89,2.96]·10^−9 for the M-series correction beyond 10^7; the latter comes from |θ(t)/t−1|<.001 by CH2 Lemma 9.2/Cor.1.3 and Dusart 4.5, with tests in d02_mcheck.py. Counters fit: the reciprocal prefixes are <5 for x≤3·10^11 by Dusart 5.6 with M≤γ<1, even for small x by monotonicity; the largest wide log/target products fit in 128 bits. Segment marking starts at p² or the first appropriate multiple, so every odd composite is hit by a base prime. Neighboring blocks are linked by the sequential cell checks.

An exit status of zero is not enough. The text reports a certified suffix: take only [verified_suffix,top]. The .011 run from 3·10^9 gives suffix 3909288921, with unresolved cells before it. All six stricter invocations report zero failed cells and suffix equal to the requested onset. A separate .011 full run from 4760000000 also passed using the looser M estimator and a finer mesh. No earlier failure of an interval sufficient test is asserted to be an actual violation.

## Whole-domain analytic joins and signed envelopes

For L≥18 set s=e^−L/2, t=e^−2L/3, X=e^−L, w=(L+1)/L², α=.000000147, ε=.0001, η=1.78. In the D02 signed bounds combine the original D01 low reciprocal-square total .0463 (d01_smooth.md S1), the D02 high total 3.2e−12 (d02_smoothing.md using CH2 App.B), and one further integration by parts in the nonconstant weight. This yields
`|∫_L^∞ dψ(v)w(v)dv| ≤ w(L)[.048 s+3.3e−12 e^−L/8+2X]`
for dψ(v)=ψ(e^v)e^−v−1. The low and high multipliers are at most 1+2|w'|/(14w) and 1+2|w'|/(Hw), respectively; the trivial term is integrated absolutely. For weight 1 use .083s+3.2e−12e^−L/8+2X or the stronger applicable D01 envelope. D01's spectral G bound on the high coefficients can be used wherever it is sharper. By Dusart Prop.4.3 and Cor.4.5 the deviation ξ in (ψ−θ)(e^v)e^−v=e^−v/2+ξ lies between −ε e^−v/2 and α e^−v/2+η e^−2v/3. Substitution into the two θ tail identities gives the D02 signed U_j,W_j expressions with the sharpened errors; the leading prime-power biases are B1=(1/2)∫_L^∞ e^−v/2 dv/v and B2=s. The signed 20≤L≤29.9 slab is retained, including opposite signs for the normalized Q and P. No all-ray sign is claimed.

On 18≤L≤29.9, two integrations by parts give \(B1≤(s/L)(1−2/L+8/L²)≤BI·s/L\) for BI=1−2/29.9+8/29.9² (its comparison multiplier increases there). With the one-sided CH2 Lemma 9.2 ψ bounds .751/.791, the common absolute log-product/D1 cap u(L) in m_repair.py uses BI, .791 and the upper ξ integral on the upper sign; on the lower sign it uses .751 and drops the nonnegative B1, debiting at most X for the log-product correction. The code adds X on both signs for convenience. Each L³-scaled term is a nonnegative polynomial times a negative exponential, already decreasing at L=18 (the slow exp(−L/8) has degree at most 2). Unscaled u also decreases, so L³u/(1−u) decreases. The checked log onsets 22.9,23.1,23.28,23.6,24,24.285,24.82 join the seven finite tops, with the required exponential comparisons tested exactly.

On [29.9,40] use the D01 moderate π transfer with 6.31 instead of 6.6: the original PT displayed bracket is <6.31/3 there. Integrate only to exp(40), retaining the right residual <7e−9 from D01. A scaled common log/D1 cap is \(6.31 L²e^−L/2+5L³e^−L+7e−9 L³\); it is convex on the slab, by the derivative sign of each term L^m exp(−aL) (second derivative sign (aL−m)^2−m). Compare endpoints, also using 32 for the .001 ray. On [40,190] use the D01 weighted CH2 transfer with the constant part at most 2D·190² (D=1.048e−12). On L≥190 the D01 .01955 pure power bound closes all links. This avoids replacing the favorable near-29.9 envelope by a coarser finite ψ estimate. m_repair.py checks all pieces and the two analytic-only rows.

Smaller uniform caps simultaneously for the products/D1 (L^−3) and D2 (L^−2) are 4.4e−6, 8.2e−8, 4.3e−8 from inclusive L=50,60,65. On [50,190] combine pointwise θ cap \(D+116s\) with integrated absolute cap \(2.0860003s+2.67t+3.3e−12 e^−L/8+2X\) times the appropriate weight. Debit X for the products. Bound the scaled plateau DL² at 190 and every other term by its value at the desired left endpoint, justified by decreasing polynomial-exponential factors. Conversion can use v/(1−v) with v the scaled log cap; the unscaled cap is smaller. The D01 power bound closes the comparisons from 190. This is distinct from the stronger pointwise envelope.

## Prime-power logarithm correction and power profile

Exactly Z_Q=D1−T(x) for \(T=\sum_{p>x,k≥2}1/(k p^k)\). Let \(I=\int_x^\infty du/(u²\log u)\) and let δθ(x) bound |θ(u)/u−1| on u≥x (use .001 for L≥18, and also the decreasing power-θ bound for larger L). For \(g(u)=1/(u²\log u)\), Stieltjes summation on (x,∞) gives
`|∑_{p>x}p^−2−I| ≤ δθ(x)(2xg(x)+I) ≤ 3δθ(x)/(xL).`
The k≥3 tail is nonnegative and at most \((\sum_{p>x}p^{-2})/[3(x−1)]\). Since (1−1/L)/(xL)≤I≤1/(xL), at all L≥18
`.470/(xL)<T(x)<.502/(xL).`
More precisely with \(a=3δθ(x)/(xL)\) use \(T∈[I/2−a/2,I/2+a/2+(I+a)/(3(x−1))]\). If D1∈[d_−,d_+] then \(Z_Q∈[\ell,b]=[d_−−T_{max},d_+−T_{min}]\). The two errors for Q and P are bounded by max(e^b−1,1−e^ℓ) and max(e^(−ℓ)−1,1−e^(−b)), respectively. Compared with the previous [0,1/(2 floor x)] correction, both ends tighten for the same D1 interval. The minimum with other branches may be sharper still.

The descending whole-ray coefficients below multiply \(x^{-1/8}/L\) for products and D1 and \(x^{-1/8}\) for D2:
```
L onset     coefficient
190         .01955 (inherited)
400         .01361 (inherited)
600         .01231
900         .01164
1300        .01127
2000        .01099
3500        .01078
9000        .01059
12000       .01055
18000       .01052
```
The refined coefficient C*(L) is in density_refine.md. Combine the θ endpoint and the absolute integral bounds in units x^−1/8, with normalization by 1/L for D1 and log product. A shared coefficient is
`U=C*+(1+1/L)[2.0860003 e^(−3L/8)+2.67 e^(−13L/24)+3.3e−12+2e^(−7L/8)] + L e^(−7L/8).`
Use \(U/(1-Ue^{-L/8}/L)\) for both product errors after conversion, and U for the sums. The coefficient terms and correction in the denominator decrease on these rays, validating all real tail comparisons. Retain the pointwise whole function as well as these simpler constants. The bottleneck of this method for more decay or another log factor is the local θ endpoint; the proved weighted integral has a much smaller coefficient, and separately recentering at an observed θ yields D01's small integrated residual, not an artificial improvement to the requested quantities. The exact current assumption cannot change any frontier relative to complete B0 since it is implied by B0.
