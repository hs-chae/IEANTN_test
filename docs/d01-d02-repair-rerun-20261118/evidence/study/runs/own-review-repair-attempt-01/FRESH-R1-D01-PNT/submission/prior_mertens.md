# Mertens products and both prime sums

Definitions (all real x≥2, primes at the right endpoint included):
[
 egin{aligned}
 M&=gamma-sum_psum_{kge2}1/(kp^k),&
 B_3&=gamma+sum_plog p/[p(p-1)],\
 r&=sum_{ple x}1/p-loglog x-M,&
 w&=sum_{ple x}log p/p-log x+B_3,\
 z&=log Q_{
m raw}(x)-gamma-loglog x,&
 e^{z}&=e^{-gamma}Q_{
m raw}(x)/log x,quad
 e^{-z}=e^gamma(log x)P_{
m raw}(x).
 end{aligned}
]
The constants are those of Dusart 2018 Theorems 5.6–5.7 (PDF pp.17–19). In particular the raw product errors are not two independently estimated trials.

## Whole-ray results, with real inclusive onsets

The table below gives ceilings (c/L^3) for both product relative errors and |r| (except the products-only entry), and (d/L^2) for |w|. A blank means the row does not claim that estimate. Every applicable earlier/larger coefficient remains valid. The main claims are non-strict; the finite arithmetic deliberately verifies sufficient upper/lower conditions with slack.

| x≥ | c | d |
|--:|--:|--:|
|912559.999| |.300|
|1000000| |.297|
|1530000| |.250|
|2278381.900|.200 (products only)| |
|2278382.200|.200| |
|2278395|.199|.215|
|3451810|.190|.213|
|3459000|.180|.212|
|3462000|.170|.211|
|3475000|.160|.200|
|5010000|.150|.163|
|7110000|.140|.151|
|7130000|.130|.150|
|8800000|.125|.140|
|13000000|.120|.123|
|14000000|.100|.110|
|18003000| |.100|
|18010000|.095| |
|18500000|.090|.095|
|30912000|.087| |
|30923000|.087|.090|
|33000000|.087|.089|
|38000000|.087|.088|
|50000000|.087|.087|

Additional analytic whole-ray entries, with **both** c and d equal to the listed coefficient:
   
| x≥ |64000000|82000000|115000000|180000000|300000000|600000000|
|--|--:|--:|--:|--:|--:|--:|
| c=d |.0868|.079|.070|.060|.050|.040|
   
On the closed strip (64000000\le x\le10^{13}), one also has ( |w|\le2.151/\sqrt x) and (|r|,|e^{z}-1|,|e^{-z}-1|\le2.151/(\sqrt x L)). On the much later rays, stronger shapes hold:
[
 egin{array}{ll}
 xge e^{400}: & |w|le .014 x^{-1/8},quad
    |r|, |e^z-1|, |e^{-z}-1|le .014,x^{-1/8}/L;\
 xge e^{500}quad	ext{(basic fallback)}:
       & |w|le .005001 x^{-1/8}L^2,quad
    |r|, |e^z-1|, |e^{-z}-1|le .005001,x^{-1/8}L .
 end{array}
]
The density-branch tradeoffs for the same (x^{-1/8}) weighted and (x^{-1/8}/L) unweighted shapes are:
   
| log onset |200|224|272|312|376|493|773|2354|4321|32507|
|--|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| coefficient |.020|.018|.016|.015|.014|.013|.012|.011|.0108|.0106|
   
Neither line is a replacement for the following pointwise envelope. On the density branch its leading constant tends to .010570000003 for w and for L times the other errors, after scaling by x^(1/8). These are explicit upper-bound shapes, not assertion of an asymptotic equivalent to the actual errors. Both use only B0; the basic route and the finite joins do not depend on the FKS density table.

## Analytic pointwise envelope

Let (K(x)=psi(x)-	heta(x)). Define nonnegative tails
[
 W(x)=sum_{p^k>x, kge2}log p/p^k,quad
 U(x)=sum_{p^k>x, kge2}1/(kp^k),quad V(x)=U(x)-sum_{p>x,kge2}1/(kp^k).
]
Here V is exactly the tail restricted to p≤x. Write (b=b(L)) for the best available pointwise (|E(x)|/x) bound among the source functions in foundation.md. The signed version replaces ([-b,b]) by the intersection of all respective relative-error intervals (in particular the coth-centered CH2 interval). In addition:
[
 egin{aligned}
 w &= E(x)/x-int_x^infty E(t)t^{-2}dt+W,\
 r &= E(x)/(xL)-int_x^infty E(t)t^{-2}(1+log t)/log^2t,dt+U,\
 z &= E(x)/(xL)-int_x^infty E(t)t^{-2}(1+log t)/log^2t,dt+V .
 end{aligned}
]
The first two identities follow from the θ partial summation identities in Dusart's proofs of Theorems 5.6 and 5.7 on replacing θ by ψ−K. Each term in K yields a discrete tail at the points strictly above x: this is Stieltjes integration by parts with the included right endpoint. The last identity uses (z=r-sum_{p>x,kge2}1/(kp^k)). For the integrals involving E use respectively d(L) and d(L)(1+1/L)/L from foundation.md, or use the integral of the pointwise absolute majorant when that is smaller. Thus in particular (ignoring signed improvements)
[
 |w|le b+d+W_{
m ub},qquad |r|, |z|le
 Z:=[b+d(1+1/L)+W_{
m ub}]/L . 	ag{M1}
]
The template records an interval, not merely Z: with the symmetric error bounds the intervals are ([-b-d,b+d+W_{
m ub}]), ([-b/L-d(1+1/L)/L,b/L+d(1+1/L)/L+U_{
m ub}]) and the corresponding interval with (V_{
m ub}) for z. Upper bounds on the two tails can always start at (U_{
m ub}=V_{
m ub}=W_{
m ub}/L) since (klog p>L); lower bounds of zero are always available. If needed for x<64 million, use the finite envelope below rather than (M1).

**Power-tail upper bounds.** Put y=x^(1/3), v=x^(1/2), (eta_j=3.965/log^2 j). Dusart Theorem 4.2 gives (|	heta(t)-t|/t≤eta_j) for t≥j≥2. For v between sqrt(64000000) and e^58 we may replace (eta_v) by its minimum with ((log v)^2v^{-1/2}/(8pi)). The finite RH estimate is decreasing in t there; on t≥e^58 use the decreasing Gas plus Dusart Corollary 4.5 at the join, which is smaller than the finite RH majorant there (certified). Partial integration gives
[
 W_{
m ub}= (1+3eta_v)/v+
    x^{-2/3}left[2(1+eta_y)+{.5+2.5eta_yover1-1/y}
ight]. 	ag{M2}
]
The k=2 tail uses (int_{(v,infty)}t^{-2}d	heta(t)). For k≥3 and p≤y, the first allowed power gives p^-k<1/x and the geometric factor ≤2, so that group contributes ≤2θ(y)/x. For p>y sum powers from k=3 and bound the geometric factor by 1/(1−1/y), using ∫t^-3 dθ(t). In general the integral ∫_(j,∞) t^-k dθ(t) is bounded above by (j^{1-k}[(k-1)^{-1}+(1+k/(k-1))eta_j]), and below by the expression with minus instead of plus. The nonnegative lower bound (max(0,1-3eta_v)/v) can thus be added to the w interval.

For a tighter log-tail upper bound use k=2 exactly as (	frac12int_{(v,infty)}(t^{-2}/log t)d	heta(t)), and use the k≥3 part of (M2) divided by L. More explicitly the k=2 upper bound is
[
 	frac12left{ int_v^infty {dtover t^2log t}+
  eta_vleft[{1over vlog v}+int_v^infty {2+1/log tover t^2log t},dt
ight]
ight}.
]
The analogous lower bound (changing +η to −η, max with zero) also applies to U. To transfer it to V subtract at most (1/(2lfloor x
floor)), since (sum_{p>x,kge2}1/(kp^k)lesum_{n>x}1/[2n(n-1)]). The upper bound for V is at most the upper bound for U. These replacements improve the complete pointwise intervals by intersections, with no crossover undecided by a sampled grid.

**Other source branches retained.** When θ has a relative bound e_θ(t) on the whole forward domain, put
[
 a_w=e_	heta(x)+int_x^infty e_	heta(t)dt/t,qquad
 a_r=e_	heta(x)/L+int_x^infty e_	heta(t)(1+log t)/(tlog^2t)dt .
]
Keep intervals ([-a_w,a_w]), ([-a_r,a_r]), ([-a_r-1/(2lfloor x
floor),a_r]) for w,r,z. For (e_	heta=eta/L^k), (k>1), these have the explicit expressions (eta[(k-1)^{-1}+L^{-1}]/L^{k-1}), (eta[k^{-1}+(1+1/(k+1))/L]/L^k). This retains the Dusart k=4 branch and every eligible row in Theorem 4.2, not just k=3. The integral can instead use a piecewise pointwise minimum of the θ branches, including the finite-RH bound, the ψ bounds with power subtraction, and the best Dusart row at each t. Another option starts from the centered sum (Z_1=sum_{nle x}Lambda(n)/n-log x+gamma). CH2 Corollaries 1.2–1.3 give pointwise majorants, and (M1) gives (b+d) for |Z_1|. Preserve their minimum B_1(t). The identity (Z_1=E(x)/x-int_x^infty E/t^2) gives the alternative shared error for r,z as (Z_1(x)/L-int_x^infty Z_1(t)/(tlog^2t)dt) by integration by parts. Thus (B_1(x)/L+int_x^infty B_1(t)/(tlog^2t)dt) can also be minimized with the other shared-error majorants. This uses the centered weighted CH2 branch even when the absolute ψ derivative route is not best.

**Definition of the full envelope.** Intersect the applicable intervals for r,w,z from the preceding formulas and the finite intervals below; for any scalar error interval [a,b] take max(|a|,|b|). For the product errors on a z interval [a,b], use respectively (max(|e^{-a}-1|,|e^{-b}-1|)), (max(|e^a-1|,|e^b-1|)). Minimize each resulting error bound with the relevant table entries, power-ray bounds, and the old direct Dusart Theorems 5.6–5.9. Thus the original .2/L³ product branch from 2278382, .2/L³ reciprocal branch from 2278383 and .3/L² weighted branch from 912560 are never discarded unless dominated. Integrals in the envelope are explicit convergent real integrals of the stated functions or their minima. Retaining both endpoint signs for z prevents a forced symmetry loss in the reciprocal products. The more elementary symmetric consequence (e^Z-1≤Z/(1-Z)) for 0≤Z<1 is used for the coefficient tables.

## Finite certificate and analytic joins

Set J=64000000 (named N in finite.cpp). Compute the exact primes ≤J by an Eratosthenes sieve. To approximate the constants use:
* (H_n-log n-1/(2n)legammale H_n-log n-1/(2n)+1/n^2), n=10^6. This follows from the trapezoid error for 1/t on each [j,j+1]; convexity gives nonnegative error and the summed errors are ≤(sum_{jge n}2/(12j^3)≤1/n^2).
* The prime tails at J of the series subtracted from γ for M and added to γ for B_3 lie in ([.465,.502]/(Jlog J)) and ([.997,1.003]/J), respectively. In CH2 Lemma 9.2's ψ range and thereafter with Gas, subtracting Dusart Corollary 4.5 shows (|	heta(t)-t|≤.0003t) for all t≥J, checked at J and 10^13, with monotone components. For B_3 integrate t^-2 against dθ and bound the factor (1−1/p)^-1 between 1 and (1−1/J)^-1. For M the k=2 main integral is (	frac12int_J^infty dt/(t^2log t)), between ((1-1/log J)/(2Jlog J)) and (1/(2Jlog J)) (use 1/(1+s)≥1−s). Add/subtract the tail error with η=.0003 as above. For k≥3, use (sum_{k≥3}1/(kp^k)≤(1/J)sum_{k≥2}1/(kp^k)): hence the all-k upper bound is obtained by multiplying the k=2 upper bound by (1−1/J)^-1. The interval is still inside [.465,.502], by the rounded inequalities in check.py and mertens_check.py.

**Finite pointwise branch.** The elementary finite prescription that applies even for x<the table onsets is: sum the finite prime series at x using the sieve to J, compute the intervals for the constants as just described, then subtract/shift by exact (log x) and (loglog x) to enclose r,w,z. This gives a rigorous pointwise interval on 2≤x≤J (one can either use exact finite sums and logarithms or the fixed-point arithmetic below); no interpolation or numerical sample is its foundation. It may be intersected with every applicable analytic or original estimate. The following finite check compresses this into useful whole-ray constants without enumerating real inputs.

**Integer calculations.** In finite.cpp, scale (S=2^{56}); all rounded limits are signed 128-bit integers. The log kernel is (2sum z^{2j+1}/(2j+1)) through degree 39, based on (z=(u-1)/(u+1)) after reducing 1≤u<2. All computed terms round down. For fixed input z≤1/3 the power recurrence error is ≤2 units (multiply by z²≤1/9 and allow one unit each for z² and the step), per-term division loses <1, and the omitted geometric tail is <1 unit of S. Rounding z itself changes the true log by <3 units. Thus the interval +128 units safely encloses the error for one such series. Normalization by power-of-two shift loses <2 units in the reduced log; at most 25 log 2 contributions give the +4096 unit width. For the positive q increments use (z=1/(2p-1)) in the same series. For the M-series per prime, loop until (p^j>S), rounding each term down: accumulated floor loss is <j−2 and omitted scaled tail is ≤1, so +j encloses it. Every operation used for the interval estimates is exact integer arithmetic with upper or lower rounding; bounds on operands from the program (L<18, centered error endpoints below S, p and N under 2^26, all test coefficients ≤300) suffice for each intermediate magnitude <2^127. There is no binary floating-point dependency.

On a gap with a fixed set of counted primes the weighted error is c−L, and reciprocal and log-product errors are c−log L. Their signed products by L² and L³ respectively have derivative sign determined by (2(c-L)-L) and (3(c-log L)-1). The exact interval checks at the left endpoint ensure negativity across each gap. The absolute scaled values are therefore bounded by the maxima of the two endpoint values, including the left limit at the next prime. The next gap includes that prime's right value. The code handles a rational inclusive onset inside a gap by checking that endpoint directly. For products the denominator (1-max|z|) comes from both endpoints of the gap and bounds the exponential loss via (e^{|z|}-1≤|z|/(1-|z|)). Distinct sign tests for the other sums use their own respective endpoint powers. N is composite here and the last gap includes it. Executable receipts are in finite_evidence.txt and finite_trials_evidence.txt.

**Analytic join.** On L∈[log J,log 10^13] take b=.791e^-L/2; with (M2) and its refined square-root error, the ceilings L²(b+d+W_ub) and L³ Z/(1−Z) are nonincreasing. The products L²e^-αL all decrease there for α≥1/8, and so do the positive rational factors in (M2); where the extra θ square-root bound is allowed it is decreasing as well. The certification at J gives ceilings <.087 for both. Monotonicity also establishes the post-sieve coefficients by checking their left endpoints, with the remaining joins below .040. For the square-root strip simply multiply the weighted and log-normalized estimates by e^(L/2); bound the scaled high-zero part of d at the right endpoint and every other nonconstant factor at the left endpoint, then include the product denominator using the left endpoint. Then use Gas through L=110 (through 200 in basic mode), bounding its constant times L² by the value at the right endpoint and every decreasing term at the left; the resulting <.04 numerator and corrected ratio are verified. For L≥110 take q(L)e^-L/8, where q decreases; in basic mode from 200 use .005L²e^-L/8, for which L^4e^-L/8 decreases. These checks justify all finite-to-infinite joins, including the .087 ceilings. For the power-ray constants divide the weighted bound and the bound LZ by e^-L/8 (and by L² in basic mode); the extra terms are nonincreasing at the tested onsets and thereafter, and the product denominator only increases. The endpoint tests are in mertens_check.py. For L≥376, .014 L²e^-L/8 decreases and is <.087 at 376, so the power bounds are strictly stronger than every numerical table ceiling on that ray (and similarly for the basic power bound from 500).

## Comparison, attempts and limits

The whole-pointwise comparison to any lawful original envelope is a tie across the addition of D01, not an inference that a chosen weak original error must be best among all original consequences. The explicit reconstruction includes the direct Dusart envelopes, finiteRH and CH2 derived alternatives, and the FKS and QRH branches, with earlier thresholds and stronger coefficients than Dusart's direct estimates. If transferring D01 by the same (psi)-to-sums calculation, one replaces b for L≥200 by ((1/64)L^2e^{-L/8}); the basic B0 b alone is pointwise smaller and gives no reason to switch. One could also propagate it inside the tail integrals, but the stronger B0 majorant improves the same terms for every t≥e^200. Enlarging the hypothesis set cannot help through any other lawful route either, by the redundancy proof.

Serious attempts included signed endpoint verification, choosing prime-power tails by the receiving weight rather than blanket θ bounds, using the integrated oscillatory error instead of an absolute integral that costs an extra factor near the finite join, using scaled finite-degree inequalities up to every prime jump, and splitting QRH zeros by density and height. Targeted finite_trials.cpp checks fail at earlier candidate onsets (e.g. .300 at 912550, .200 from 2278381, .087 from 18500000); these are failures of sufficient interval tests, not automatically counterexamples to the proposed bounds. The weighted .100 attempt at 16000000 had 827 failed gap checks (latest right endpoint 18002111); the 18003000 repair passed. The .087 floor within the sieve strip is primarily the remaining local maxima and the simple finite coefficient grid, not a limitation of the asymptotic tail. The formulas keep more pointwise information than this table. Extending the finite certificates, certifying more efficient oscillatory zero sums, or tighter tail constants from density could improve this unconditional portfolio. No faster ultimate power from QRH's edge alone is asserted: no edge-exclusion, cancellation, or zero-spacing beyond the used premises was established. No claim of global optimality is made.
