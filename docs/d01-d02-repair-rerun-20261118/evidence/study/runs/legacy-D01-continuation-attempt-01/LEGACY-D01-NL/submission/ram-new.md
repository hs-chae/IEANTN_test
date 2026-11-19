# Ramanujan: real endpoint, quantitative envelopes and weaker source subset

Everything is stated for right-continuous prime counts. R(x)=e*x*pi(x/e)/log(x)-pi(x)^2. Write t=log x, h=x^2/t^6.

## Exact real boundary and comparison with the original endpoints

Use n=38358837682, P=1644673232, Q=632207037. The exact counts pi(n)=pi(n+1)=P and pi(floor(x/e))=Q for n<=x<=n+1 follow from two own independent algorithms (floor-quotient sieve in D01_pi_exact.py and prime-factor counting in D02_count.py with D02_cert.py). Their correctness arguments are in D01_ramanujan.md and D02_ramanujan.md. The floor is 14111427770 on the entire bracket. The signed difference e*x*Q/log x - P^2 increases on that bracket, is negative at n and positive at n+1, and its unique zero r lies strictly between 38358837682.217926 and 38358837682.217927, by exact rational endpoint tests. Moreover its derivative on this bracket exceeds 67623427 (D01_pi_exact.py), proving the stated local linear lower bound.

Use Platt–Trudgian 1809.03134v2 Theorem 2 (PDF p.3, §5) only at integers n+1 through floor(e^58) in the small range: its literal real statement contradicts the exact counts on (n,r]. For any real x in [n+1,e^58], pi(x)=pi(floor x), and x/log x and pi(x/e) are nondecreasing, so R(x)>=R(floor x)>0. This is not a new sieve at that scale. The original closed e^3915 ray is also lawful and retained; Dudek–Platt Theorem 1.2 e^9658 is weaker and their Thm 1.3 (PDF p.2) is conditional on **full RH**. Their §3.1 and Lemma 3.4 supply original finite computations with paper trust. The analytic B0 margin below starts strictly below e^58, closing the gap. On this original finite range there is also an explicit sawtooth margin: for m=floor(x), R(x)>e*632207037*(x/log x-m/log m), by the same monotonic transfer and the verified strict integer sign. At the integers this lower profile is zero. A smaller strict real positivity ray is impossible since it would contain r; the non-strict zero bound also attains equality at r and fails just to its left. The least integer starting point for the strict ray is n+1.

## Whole-ray profiles certified under B0

For a row (t0,k,w), the following strict inequality holds for every real t>=t0:

    R(x)/h(x) > sum_{j=4}^{k-1} d_j / t^(j-4) + w/t^(k-4).

The prefix coefficients d_4,...,d_13 are 1,14,145,1412,13985,145450,1610021,19063832,241691425,3277187246. Take the maximum of all applicable rows, prior proofs on their own domains and the adaptive profile G below. The exact row list (onsets are rational log values, not rounded x) is:

| t0 | k | w |
|---:|---:|---:|
| 36.88 | 4 | .05 |
| 36.96 | 4 | .09 |
| 37 | 4 | .11 |
| 38 | 4 | .50 |
| 40.23 | 4 | 1 |
| 41.25 | 5 | 5 |
| 45 | 5 | 9.7 |
| 46.8 | 5 | 13.4 |
| 47.25 | 5 | 14 |
| 47.25 | 6 | 1 |
| 47.65 | 6 | 20.5 |
| 190 | 6 | 49 |
| 200 | 6 | 112 |
| 210 | 6 | 136 |
| 219 | 6 | 145 |
| 220 | 7 | 190 |
| 240 | 7 | 1270 |
| 253 | 7 | 1412 |
| 289 | 8 | 13985 |
| 324 | 9 | 145450 |
| 350 | 10 | 1500000 |
| 360 | 10 | 1610021 |
| 397 | 11 | 19063832 |
| 432 | 12 | 241691425 |
| 480 | 13 | 3277187246 |

Some comparisons: at t0=37 the guaranteed constant rises from .05 to .11; the .05 and 1 onsets move from 36.96 and 43 to 36.88 and 40.23, respectively. With the common originals the D02 B0-only first-order coefficient 14 had onset 48.75; now it is 47.25 and there is already a positive second-order coefficient there. At the old onset 50 for coefficient 16, the new coefficient 20.5 already holds, and at fixed 16 an onset of 47.65 is sufficient. At fixed 145 the old onsets were 236 (D01) and 220 (D02 with original QRH); 219 is sufficient. At t=200 the new whole-ray coefficient 112 is stronger than all the listed older B0-only constant second-order rows there. These are comparisons of *certified margins* (an adaptive branch at a given x may be stronger than any of the simple rows). No optimality is claimed for numerical margin rows.

## Prime-count model and proof

Use li2(y)=integral_2^y du/log u. Partial summation with the initial atom convention gives exactly
    pi(y)-li2(y)=(theta(y)-y)/z+integral_2^y (theta(u)-u)/(u log^2 u)du +2/log 2,
where z=log y. For T in the finite list TS in D01_check.py, set a_T=3.142/T and let b_T be the original CH2 coefficient (log^2(T/(2*pi))-log(T/(2*pi))/3)/(2*pi) rounded upward to a hundredth. CH2 Cor.1.2 (p.3), Lemma 9.2 (p.35) and the centre correction yield |psi(u)-u|<=a_T*u+b_T*sqrt(u) for u>=2, as in D01_ramanujan.md; the rational centre tests are in D01_check.py. For the upper theta error use b_T-.9999 (Dusart Prop. 4.3, p.12) plus the missing .9999 sqrt(u) below 121; for the lower theta error use b_T+1.4262 (Thm 4.2 proof, p.11).

For z>=16 the integrals of u^(alpha-1)/log^2 u through exp(16) are at most 100000 for alpha=1 and 100 for alpha=1/2 by the directed upper Riemann sums inherited in D01_check.py. Above exp(16), differentiation of exp(alpha*z)/z^2 gives the respective upper factors 1/(1-2/16)=8/7 and 1/(1/2-2/16)=8/3 times exp(alpha*z)/z^2. Hence for both signs the normalized pi radius for (pi-li2)*z/y is

    r_T(z)=a_T(1+8/(7z))+B_T(1+8/(3z))e^(-z/2)
                     +(100000*a_T+100*B_T+50)z e^(-z),

where B_T is the indicated upper or lower choice of coefficient. The fixed 50 covers 2/log 2 and the exceptional prefix below 121 (bounded by 2/log 2+22/log^2 2<50). For the upper side also use 2z e^(-z) through z=43.749 inclusive. Here use the documented pi<li_PV range 2<=x<=10^19 of Platt–Trudgian FiniteRH §3.3 (PDF p.5, their reported Bue the result at original trust), which is stronger than the earlier 1.2e17 quoted in Dudek–Platt. One has li_PV(2)<2: in log coordinates integrate on [-1,log 2] after subtracting 1 in the numerator, bound (e^s-1)/s by 1 and 1/log 2 respectively on the negative and nonnegative pieces; log log 2 and the far negative integral are negative. Thus there is no hidden change of normalization. Check e^43.749<10^19 in ram.py. At or just beyond the transition all finite cells are covered, including the fallback branch when the sign estimate is not available.

For the symmetric extra radius in ram.py, use a=1.048e-12, B=115.1 and b=7/8, y_b=186.09. The CH2 Cor.1.3 and Dusart prime-power error yield a+B e^(-z/2) for the absolute relative theta error. By power.md and the check C_b(y_b)e^(-(1-b)y_b)<a, the plateau a can be replaced at all real z>=log 2 by

    D_b(z)=a*exp[-(1-b)(z-y_b)_+].

Indeed above the switch C_b decreases and the prime-power term costs at most B e^(-z/2). The normalized pi radius resulting from D_b and the square-root term is

    r_b(z)=B(1+8/(3z))e^(-z/2)+D_b(z)(1+7/(5z))
                         +(100000*a+100*B+3)z e^(-z).

To see the last factor for D_b, on s>=16 use D_b(s)/D_b(z)<=exp[(1-b)(z-s)] and (z/s)^2<=exp[2(z-s)/16] for s<=z. The factor in the integral is at most (1-(1-b)-2/16)^(-1)<7/5 even for b=27/32. The prefix constants follow just as before; 2/log 2<3. Take r_+,r_- as separate pointwise minima, using available signs, with or without r_b as appropriate. Omitting r_b is lawful in the no-QRH no-H branch.

Approximate z*e^(-z)*li2(e^z) by P(z)=sum_{j=0}^{14} j!/z^j, using

    P(z) < z*e^(-z)*li2(e^z) < P(z)+C/z^15       (z>=24),
    C=4*15!.

The inequalities at 24 are checked using the convergent integral expansion
    li2(e^z)=log(z/log 2)+sum_{m>=1} (z^m-(log 2)^m)/(m*m!).
The tail from m=121 at 24 is below 2*24^121/(121*121!)<1e-32 by term ratios. Thereafter differentiate e^z*P(z)/z: it misses e^z/z by 15!*e^z/z^16; the upper correcting term has derivative C*(1-16/z)*e^z/z^16, more than that deficit. This is a two-sided anchored enclosure, not divergent-series extrapolation.

The normalized main expression is t^4[(t/(t-1))*P(t-1)-P(t)^2]. Expand the first term to degree 28 in 1/t, all coefficients of the omitted series being positive. For degrees n=0,...,28 the difference coefficients are
    d_n=sum_{j<=min(n,14)} j!*binom(n,j)
             -sum_{0<=j<=14,0<=n-j<=14} j!*(n-j)! .
The low four vanish. The signed loss due to pi errors and li's upper remainder is at most

    E(t)=[2P(t)+C/t^15+r_+(t)]*[C/t^11+t^4*r_+(t)]
                    + t^5*r_-(t-1)/(t-1).

Indeed the shifted lower count is linear, while the upper count is nonnegative and its square differs from P(t)^2 by the indicated factor. Thus an explicit pointwise lower profile for R/h is
    G_b(t)=sum_{n=4}^{28} d_n/t^(n-4)-E(t)
on the entire real ray t>=36.88. Strictness follows already from the positive truncated main-series tail (also from the strict li enclosure). The factor 2P(t)+C/t^15+r_+ avoids paying a fixed worst-case constant in the middle range. The older D01 and D02 exact functions, wherever lawful, can also be retained by a maximum.

Finite comparison cells in ram.py use outward arithmetic, with a subdivision whenever a whole closed cell cannot be certified directly. The upper bound for a radius on a cell may use a single choice good over the entire cell, rather than the pointwise optimum. A box containing the crossover of the pi sign branch is split, and the right cell uses a lawful fallback including its own left endpoint. Each comparison then continues on the entire infinite tail: for an anchor U>=300 from the row list, replace both r bounds by r_b. Subtract the desired prefix. Pay the losses and every negative coefficient by either the excess d_k-w>0 at degree k, or by d_(k+1)>0 when d_k=w. Multiply costs by t^(j-4) for that paying degree j. All costs then decrease: reciprocal powers have positive decay powers, the extra factor 2P+C/t^15+r_b decreases, each remaining exponential rate is >=1/8 once past both switches, and for t or t-1 factors the sum of positive exponents is <=j+2 (hence log derivative <=(j+2)/(t-1)-1/8<0). The anchored finite tests are strict. This proves the whole real rays. The same method for the actual signed gap via the li enclosure gives the successive asymptotic coefficients through t^(-9) with O(t^(-10)) and explicit one-sided remainders; no asymptotic is needed for the comparisons.

## Separate weakening of premises: no QRH and no H

The same finite proof without r_b gives positivity up to t=754 inclusive, starting at 36.88, so it joins the integer-origin interval and the exact local root. On the later side use D02_ramanujan.md's FKS Table 5 interpolation (PDF p.22, rows 3000 and 4000) and Theorem 3.2, then FKS Theorem 1.2 and Table 6 at 4000. It is the positive zero sum at a fixed truncation that is log-convex, not the signed prime-count error. The resulting late loss E_L is nonincreasing (proof in the inherited file). Its main polynomial is >1+14/t for t>=40 by the 145/t^2 term and a bound <1/t^2 on the negative terms. The exact late.py checks use 1+14/3041 through 3041 and 1 thereafter, not a single isolated test. On t>=3039.2 the margin is .0005; on t>=3040, .004; on t>=3200, .50; t>=3500, .89; and t>=4000, .98. The own old margins .08 at 3060 and .23 at 3100 remain available. All these rays are strict. Thus the no-QRH gap has been shortened but not fully joined: the residual unproved window for that premise subset is (754,3039.2) in t. With B0 there is no residual window.

Failed routes are specific to method, not counterexamples: the strengthened CH2 absolute-radius lower bound is already negative at 755 (certified upper enclosure for that lower-bound expression in late.py); the plateau error cost at 1000 is >3 in the normalized scale 3*a*t^4. Using the native FKS table error at t=2000 in the same transfer costs >100, and using the 2900 row still costs >1. The certified late interpolation and sharper main polynomial did improve the previous 3041 boundary but cannot reach the early region. The missing ingredient without QRH is a much smaller two-point absolute error (on this scale roughly 1/(3*t^4)), or a new signed correlation argument for these errors; discarding QRH is optional and not required by the original-input envelope. No independent reproduction of the published FKS Table 5 zero counts was performed.
