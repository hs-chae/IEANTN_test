# Common new proof: weighted zero mass and log-interval averaging

Put t=log x. B0 is exactly the seven originals. Use b=7/8 in B0 by OpenAIQRH Theorem 1.1, PDF p.4 (its stated zeta consequence). With D02 use b=27/32. Indeed for Re s>1,
[
 -\zeta'/\zeta(s)=s/(s-1)+s\int_1^\infty(\psi(u)-u)u^{-s-1}\,du .
]
The given real-ray majorant makes the integral holomorphic on Re s>b: the finite prefix is harmless and every compact subregion has an integrable tail even after differentiation. The zeta function continues there (for Re s>0 use the integral of the fractional part in the Euler summation formula). The identity continues meromorphically; no zero can give an unaccounted pole in the open half-plane. This proves only Re rho<=b, not a strict inequality. D02 implies D01 directly and can also be used in lieu of the QRH premise in this strip argument. No premise asserting full RH is used. Notably this argument can change estimates for t<200 through the inferred global strip, without evaluating the D02 point majorant there.

## Two moments

Use H=3000175332800, FiniteRH Theorem 1, PDF p.2, and H_f=3e12. Let s0=3/4. For sigma in [s0,b] set p=(8/3)(1-sigma), q=5-2sigma. For positive ordinates, Dusart2018 §2.2.2 Theorem 2.3, PDF p.5, gives a bound
[
 N(\sigma,u)\le c_1 u^p(\log u)^q+c_2(\log u)^2,qquad
 (c_1,c_2)=(4.9\,3^p,51.5).
]
Here use log(1+v)<=v. A second pair at each sigma is FKS Cor.2.9 and Table 8, PDF pp.7–8 and 26 (the a1=.77 half, inflated upward in spectral.py). We invoke the published corollary/table at its original trust, not the raw parameters in Theorem 2.7. The conclusion counts beta>=sigma. The strict height convention makes no difference to the integrals. Use H for Dusart and H_f for FKS. Both remove all ordinates <= the respective height for beta>=s0.

For m=1,2 an upper bound on twice the positive inverse-m-th ordinate moment is
[
 d_m(\sigma)=2m\left[
 c_1\frac{e^{-zA}A^q}{z}\sum_{j=0}^4\frac{(q)_j}{(zA)^j}
 +c_2\frac{A^2+2A/m+2/m^2}{m H_*^m}
 \right],\qquad A=\log H_*,\ z=m-p .
]
Indeed sum the integral of m/u^(m+1) from each ordinate out to infinity using nonnegativity, then put log u=A+v. The fourth Taylor polynomial of (A+v)^q is an upper bound on v>=0 because 3<q<4. falling factorials are (q)_j=q(q−1)...(q−j+1). All signs and powers are as in power.md; the m=2 recipe in smoothed.py is new. The two upper bounds can be minimized. Any upstream bound in sigma also bounds a downstream moment; hence taking prefix minima of upward dyadic/decimal-grid values is valid even if a table transition gave an upward jump.

Use the common nested mesh {s0+i/4096} plus the FKS table boundaries, cut exactly at b. If s_i are its nodes and D_i the chosen cumulative majorants at s_i, the bound for the weighted moment relative to x is
[
 B_{b,m}(t)=D_0 e^{-(1-s_1)t}+
 \sum_{i=1}^{n-1}D_i(e^{-(1-s_{i+1})t}-e^{-(1-s_i)t}) .
]
The proof is to bound the increasing test function by its next-node value, with the last beta=b included. Equivalently telescope to a sum of nonnegative multiples of exponentials. No individual bin is bounded by subtracting cumulative upper bounds. Implementation performs exactly this telescoping and evaluates consecutive exponential factors by multiplication. The mesh is nested for the two b values, with the J endpoint a Q node. Consequently narrowing b strictly reduces each of these moment bounds for t>0; the same holds for the inherited Dusart-only staircase of power.md. A minimum of the two common-mesh variants is also strictly reduced. These are statements about the bounds, not about comparable values of the actual error in different universes.

For t>=80 use the point bound in power.md with B_{b,1} in place of its high part (FKS Theorem 3.2, PDF p.8, T=exp(t/3), exact same validity checks and low component). Let C_b^new(t) denote this bound multiplied by exp((1-b)t) and C_b(t) the minimum with power.md's original normalized staircase. Both, and their minimum, are nonincreasing on t>=80: all high terms on this scale are positive exponentials with nonpositive rates; the low polynomial-exponent terms have negative derivatives there. The continuous original Dusart-only bound and simple bound from power.md remain available. No actual signed sum is taken to be monotone.

## One-sided averages and the new point radius

Set `K_b(t)=3.1e-12 exp(-t/4)+B_{b,2}(t)`. This bounds the absolute inverse-square weighted contribution of all ordinates above H: use CH2 Lemma B.5/(B.6), PDF p.44, for beta<3/4, and the new density moments otherwise. The same CH2 reciprocal-square bound at 3e12 is <3.1e-12 counting both signs. For t>=80, 0<h<=1, the following is a second point bound for |D(t)|=|exp(-t)psi(exp t)-1|:
[
 S_b(t,h)=e^h\big[h/2+117.02e^{-t/2}+2 K_b(t)/h+1.84e^{-t}\big].
]
To prove it compare the value of the nondecreasing function psi(exp s) at s=t to its uniform averages on [t-h,t] and [t,t+h]. This works at every real t including jumps. The mean of the main term exp s differs from exp t by at most exp(t+h)h/2 (mean displacement h/2). The integrated explicit formula is Dusart (2.1), pp.3–4. Low zeros (through H) are on the line by FiniteRH; use their unintegrated reciprocal ordinates bounded by Platt–Trudgian2021 Lemma 2, PDF p.4, at H. The scalar check certifies log^2(H/(2*pi))/6.28+1.8642<117.02. High zeros after integrating have coefficient (exp(rho h)-1)/(h rho^2) or (1-exp(-rho h))/(h rho^2), with numerator magnitude <=2e^h. Finally |log(2*pi)+(1/2)log(1-exp(-2s))|<1.84 for exp s>=100. For termwise integration on compact intervals one may use the L^2 argument in mertens-new.md: by FKS Lemma 2.1 the unit-interval count is O(log T); the dyadic block of the ordinary zero series has squared L^2 norm O(log^3(T)/T), by summing min(interval length,2/|gamma-gamma'|) for inner products, times O(T log T)/T^2. Dyadic norms sum. Its limit agrees a.e. with the classical explicit formula; after integration the series is absolutely convergent. The one-sided averages neither invoke a prime-independent jump bound for the endpoint nor adopt a half-atom convention for the reported conclusions.

For fixed h the point bound decreases as a function of t. Another allowed choice for t>=y is h=h_y exp(-(1-b)(t-y)/2). Now every term inside the bracket decays at rate at least (1-b)/2, and the prefactor e^h decreases. In particular t^2 S_b(t,h(t)) decreases once t>=4/(1-b). For convex bounds on the normalized radius on a finite interval, freeze e^h at e^h_y: exp((1-b)t) times the remaining sum is a positive linear combination of real exponentials (possibly increasing). Thus endpoint checking suffices for this common majorant. A pointwise minimum over more h values, within the legal range, is always lawful. This average does not improve the remote power rate: the optimized h/2+2K/h behaves like a constant times exp(-(1-b)t/2), slower than the unsmoothed C_b option. It is used at their finite joins instead.

## Tail kernels and exact correlations

For a>=0 define
[
 S_a^*(x)=\int_x^\infty(\psi(y)-y)y^{-2-a}dy .
]
The proof in mertens-new.md gives, on t>=80,
[
 |S_a^*(x)|\le e^{-at}J_b^{\rm ref}(t),\quad
 J_b^{\rm ref}(t)=.0462e^{-t/2}
       +\min(3.1\,10^{-12}e^{-(1-b)t},K_b(t))+1.84e^{-t}.
]
In the integrated explicit formula a zero has denominator rho(1+a−rho); for the high ordinates this has magnitude >=gamma^2. The low bound uses CH2 (B.9), PDF p.46. For t>=log 100 the inherited formula J_b of mertens-new.md, without the density refinement, is valid. An intermediate alternative is to replace K_b by 3.1e-12 exp(-t/4)+B_{b,1}(t)/H, as in spectral.py, or use the old staircase for B_{b,1}; their minimum is used in the scalar Mertens proof. Every bound is uniform in a. This permits a signed Abel envelope and a separate oscillatory-tail envelope to be intersected.

