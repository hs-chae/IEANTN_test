# A-D02: explicit prime-counting and Mertens bounds

**Reading guide.** This file gives the A-dependent sharp Ramanujan
onset, the pointwise gap, and the spectral improvement of PsiMajorant.
mertens.md gives the unconditional product and prime-sum frontiers
and sharp benchmark onsets. extensions.md gives the improved
unconditional Ramanujan ray, the A-dependent high Mertens bounds,
and the primorial and short-interval consequences.

Assumption A is the whole-real-ray PsiMajorant in INPUT_CONTRACT.json:
|ψ(x)−x| ≤ x^(27/32) log²(x)/64 for x≥e^200. No full RH.
The supplied finite-height verification and published consequences are used
at their original trust levels. See source notes below. Results labeled A
are conditional only on the input assumption plus their cited source premises.

## Ramanujan: formulas and derivation

Write L=log x, P₁₂(L)=Σ_{j=0}^{12} j!/L^j, and r(L)=4·13!/L^13+2L exp(−3L/4).
Let D(L)=(L/(L−1))P₁₂(L−1)−P₁₂(L)^2. For any available bound E(L)
on |(L/e^L)(π(e^L)−Li₂(e^L))|, with Li₂(x)=∫₂ˣ dt/log t, put H=E+r.
Then, at L≥39 (provided bounds are defined at L and L−1),
```
R(e^L) ≥ (e^(2L)/L²)[D(L)−L H(L−1)/(L−1)
                              −2 P₁₂(L) H(L)−H(L)^2].
```
No imported normalization of li is used. Substitute v=L−log t in Li₂.
On 0≤v≤3L/4 the geometric remainder after 12 is bounded by
4(v/L)^13, whose integral against e^(−v) is at most 4·13!/L^13.
The tail of the integrand on 3L/4≤v≤L−log 2 is at most
(L/log 2)e^(−3L/4)<2L e^(−3L/4). The tail of the polynomial integral
on v≥3L/4 is at most e^(−3L/4) Σ_{j≤12}(3/4)^j/(1−16/L)
≤ 4e^(−3L/4)/(1−16/L), by termwise integration and (j)_k≤12^k.
Both tails are nonnegative, so their difference is bounded by their maximum.
This proves the two-sided approximation; it works already at L≥38.

Put a₀=1.048·10^(−12), b₀=117. CH2 Cor 1.3 and Dusart Cor 4.5 give
|θ(t)−t|≤a₀t+b₀√t for every real t≥2. For L≥38 define
```
J_s(L)=exp(−(1−s)L)(1+1/(sL−4)) + 9L exp(−(1−s/2)L)/(4s)
E_C(L)=a₀J_1(L)+b₀J_(1/2)(L)+3L exp(−L).
E_RH(L)=exp(−L/2)(L²+2L)/25+1350L exp(−L)   (38≤L≤58).
```
Indeed θ-partial summation gives π−Li₂ = (θ(x)−x)/L +
∫₂ˣ (θ(t)−t)/(t log²t)dt +2/log 2. To prove J_s, split the integral
in u=log t at L/2. Below this point use u≥log 2>2/3; above it
the logarithmic derivative of exp(su)/u² is ≥s−4/L>0. For E_RH use
Platt–Trudgian Finite RH Cor 1 for θ, with 8π>25 and e^58<2.169·10^25,
and Dusart Thm 4.2 (k=0) up to t=599. Cancel log²t in the integral
on t≥599. The prefix is bounded by 3+(9/4)·597<1350.

## Removing the log-squared loss from PsiMajorant

Let b=27/32, a=5/32, H₀=3·10^12, and define
```
d_A(L)= (0.119 L/(L−97)) exp(−a L)
        +0.02 L² exp(−0.23 L)+2.091 L exp(−L/3)      (L≥160).
```
Under A, |ψ(x)−x|/x ≤ d_A(L) for L≥160. The same bound plus
1.000000147 exp(−L/2)+1.78 exp(−2L/3) holds for θ. In particular
|θ(x)−x| ≤0.284 x^b +117√x for every x≥2. Define
```
E_A(L)=0.284 J_b(L)+117 J_(1/2)(L)+3L exp(−L)      (L≥38).
```
Use the minimum of E_C, E_A, and (only on its stated domain) E_RH
for the quantitative Ramanujan result above.

**Zero strip.** For Re s>1, absolute convergence and unique factorization
give −ζ′(s)/ζ(s)=s∫₁^∞ψ(t)t^(−s−1)dt. Subtract s/(s−1). A bounds
the remaining tail by an integrable majorant locally uniformly for Re s>b,
so this difference is holomorphic there. The identity theorem and the
simple poles of the logarithmic derivative at zeros show that β≤b for
every nontrivial zero. This does not exclude β=b. The classical meromorphic
ζ is as in FKS §2 and CH2 §9. For real 0<s<1 the alternating series
(1−2^(1−s))ζ(s)=Σ_{n≥1}(−1)^(n−1)n^(−s)>0 (identity by continuation)
rules out real zeros; thus only conjugate pairs occur in the zero sum.

**Removing the logarithm loss.** Use FKS Thm 3.2, its supplied row of
parameters (40,1/2,0,2.091), with T=exp(L/3), so T⋆≤2.45T<exp(0.34L).
The admissibility inequalities hold for L≥160: T>max(51,L),
5T+2<exp(L/2). (For the first height comparison use
log(2.45)<1 and L/150≥160/150.) FKS Lemma 2.1, Remark 2.2 and
Cor 2.3 with U=100, S₀<0.593 give
2 Σ_{0<γ≤T⋆}1/γ≤0.02 L². In detail, the coefficient of the log product
in B₁ is <0.161 and 2R(100)/100<0.06; that product is
≤(log V)^2/2 for V≥U. For an inclusive endpoint take V↓T⋆. This bounds
the part with β<0.77 by 0.02 L² exp(−0.23 L).

For 0.77≤s≤b let p=(8/3)(1−s), q=5−2s, z=log H₀.
Dusart Thm 2.3 and log(1+y)≤y give
N(s,t)≤4.9·3^p t^p (log t)^q +51.5(log t)^2 for t≥H₀.
This source statement is used directly (not the FKS density table).
Finite RH excludes the zeros counted here at heights ≤H₀.
Thus 2Σ_{β≥s,γ>0}1/γ is bounded by
```
B(s)= 9.8·3^p H₀^(p−1) z^q/(1−p−q/z)
        +103 z²/[H₀(1−2/z)].
```
Indeed integrate 2N(s,t)/t² from H₀ to infinity (each zero contributes
2/γ), and set t=H₀ exp(v), using (1+v/z)^q≤exp(qv/z), similarly
for the log-squared term. The first denominator is >0.265.
The negative logarithmic derivative of the first summand is
(8/3)(log 3+z)+2log z+(8/3+2/z)/(1−p−q/z)<97.
Use z∈(28.7,28.8), log 3<1.1, log 28.8<3.37.
Since the second summand is constant and B(b)<0.119, this yields
B(s)≤0.119 exp(97(b−s)). Now express each exp((β−1)L), for β≥0.77,
as the endpoint at β=0.77 plus ∫_{0.77}^β L exp((u−1)L)du.
The resulting high-β contribution is at most
```
0.119 exp(−aL)[exp(−(L−97)(b−0.77))
       + L/(L−97)(1−exp(−(L−97)(b−0.77)))]
≤0.119 exp(−aL)L/(L−97).
```
Use |ρ|≥γ for both parts; the FKS truncation term completes d_A.
The coefficient d_A(L)exp(aL) decreases on L≥160. At L=168 it is
<0.284. For L≤168, a₀ exp(aL)<0.284 and the CH2 estimate suffices.
Cor 4.5 adds the displayed prime power errors (or absorb them into b₀).
Consequently the global θ bound and E_A hold.

In particular d_A(L)≤0.232 exp(−aL) for L≥200, strictly stronger
than A by a factor >2600 throughout the entire domain of A, and with
onset e^160 instead of e^200 (using the global nature of A to infer
the spectral restriction). The stated d_A has asymptotic coefficient
0.119. This use of A is nonlocal, not monotone substitution at small x.

## Ramanujan conclusions (certificate below)

**Sharp real onset, with an endpoint correction to the literal source.**
Let N=38358837682, P₀=1644673232, Q₀=632207037, and define x_R to be
the unique solution on (N,N+1) of
\`\`\`
e x_R Q₀/log x_R = P₀².
\`\`\`
Then under A and the **integer restriction** of the published
Platt–Trudgian finite interval, R(x)>0 for every real x>x_R.
R(x_R)=0, and x_R is the largest real counterexample to strict
positivity. The rigorous enclosure is
\`\`\`
38358837682.21792636514465772878 < x_R
                             < 38358837682.21792636514465772879.
\`\`\`
In particular the full integer ray starts at N+1 and cannot start
earlier. This vastly improves the admitted large ray e^3915,
and joins to the low finite interval after correcting its noninteger
left edge.

**Distinction from the literal baseline.** Theorem 2 at original PDF
p.3 says N<x≤e^58, as quoted in the packet. Its *literal real*
interpretation is incompatible with explicit prime counts: for example
R(N+1/10)<0. We retain its valid-for-this-argument integer restriction
as an admitted source premise, not the contradicted noninteger claim
on (N,x_R]. For all x≥N+1 with floor(x)≤e^58, use
π(x)=π(floor(x)) and monotonicity of x/log x and π(x/e) to transfer
R(x)≥R(floor(x))>0. We do not independently redo that large integer
verification. The additional source information in Dudek–Platt, §3.1
(PDF p.8), concerns the **largest integer** counterexample and is
consistent with our count.

On [N,N+1] both prime factors are constant: N+1 is divisible by 2521,
and floor(x/e)=14111427770 throughout (strict endpoint bounds).
endpoint_check.py verifies the displayed π values and the root
bracket, including a 67,000,000 lower bound on the derivative of
e x Q₀/log x, so R(x)≥67,000,000(x−x_R) for x_R≤x≤N+1.
For the prime count, the retained set of arguments is the distinct
floor quotients floor(n/k), including all small integers up to
floor(sqrt n). It is closed under v→floor(v/p). Before processing p,
the counter at v counts integers 2≤m≤v with no smaller prime factor,
plus the previously processed primes. It initially counts v−1.
The difference of counters at p and p−1 detects whether p is prime.
At a detected prime p, remove only p times a surviving cofactor ≥p:
this is the old count at floor(v/p) minus the old count at p−1.
Updates at v≥p² in descending order use old values for the arguments
on the right. This proves the sieve recurrence by induction; all
composites are eventually removed since they have a least factor
≤sqrt n. Test against the elementary sieve at all n≤500 is included.
The endpoint logarithm uses the same atanh expansion but with
60 exact rational terms and a geometric bound for the tail.

**Quantified gap independent of the low numerical source interval.**
The pointwise lower bound given above is positive everywhere for
log x≥39.75, including the endpoint (see checker). More simply,
\`\`\`
R(x)>0.01 x²/L⁶                    for L≥39.75,
R(x)>(1+14/L+60/L²) x²/L⁶          for L≥50.
\`\`\`
The first even holds unconditionally on 39.75≤L≤50 and the second
unconditionally on 50≤L≤169. The new global pointwise estimate is
two-sided if the three error terms in its right-hand side are
added instead of subtracted to form the upper bound.

## Mertens: exact transfer identities

Let S(x)=Σ_{p≤x}1/p, V(x)=Σ_{p≤x}log p/p, M and B₃ as in Dusart 5.6–5.7.
Set Δ(x)=θ(x)−x. Exact real-domain identities (x≥2) are
```
S(x)−log log x−M = Δ(x)/(xL) − ∫_x^∞ Δ(t)(1+log t)/(t² log² t) dt,
V(x)−L+B₃      = Δ(x)/x    − ∫_x^∞ Δ(t)/t² dt,
log Q(x)−γ−log L = S(x)−log L−M − Σ_(p>x)Σ_(k≥2) 1/(k p^k).
```
First two by subtracting finite partial summation formulas at infinity,
using the normalizations in Dusart Thms 5.6–5.7 and convergence (e.g. A).
Last by the geometric logarithm series and M's definition. The double
tail is in (0,1/(2 floor x)] by telescoping Σ_{n>floor x}1/[2n(n−1)].
If |log Q−γ−log L|≤z, both relative errors are ≤e^z−1, with individual
asymmetric intervals obtainable by exponentiating the signed log interval.

Another transfer: let F(t)=Σ_{n≤t}Λ(n)/n−log t+γ. CH2 Cor 1.3 gives
|F(t)|≤π/(3·10^12)+113.67/√t (t≥1). Then
```
Σ_(n≤x) Λ(n)/(n log n) − log L − γ
     = F(x)/L − ∫_x^∞ F(t)/(t log² t)dt .
```
(The sum starts at n=2.) The constant here follows from the preceding
Mertens identity since the terms excluded at p^k>x, p≤x, k≥2 tend to zero
by dominated convergence. The extra prime-power tail when replacing this
sum by log Q is positive and bounded by the analogous sum over n≥2,
k≥2, n^k>x. It will be estimated separately.


## Ramanujan ray certification

For t=1/L∈(0,1), expansion gives
(L/(L−1))P₁₂(L−1)=Σ_{j=0}^{12} j! t^j/(1−t)^(j+1).
The coefficient of t^n for 0≤n≤12 is Σ_{j≤n} j! binom(n,j);
subtract the convolution coefficients of P₁₂². For n=0,1,2,3
the difference is zero; for n=4,5,6,7 it is 1,14,145,1412.
The remaining differences up to n=12 are positive. Ignoring positive
terms beyond n=12 in the first series and bounding the tail of P₁₂²,
\`\`\`
L⁴D(L) ≥ 1+14/L+145/L²+1412/L³ − K/L⁹,   K<1276000000 (L≥38).
\`\`\`
Here K=Σ_{n=13}^{24} [t^n]P₁₂(1/t)^2 /38^(n−13), interpreted
as a polynomial in t. Also P₁₂≤1+2/L by a geometric bound on the
terms with j≥2 (each ratio ≤12/L).
ray_check.py checks the gap on closed intervals covering [39.75,169].
To bound a positive quantity over [l,r], polynomial factors and
decreasing exponentials are bounded separately at r and l,
respectively. This is interval covering, not inference from samples.
Only E_C and E_RH are needed here.

On [169,∞) use E_A+r at arguments L and L−1. Multiplying the loss by
L⁶ gives a decreasing bound: each summand in L⁶(E_A+r)(L−h),
h=0 or 1, decreases term by term. For the exponentially decaying
terms use their largest positive log derivative contribution
6/L+1/(L−h)≤6/169+1/168<5/32, and the other factors
(1+1/(s(L−h)−4)) are decreasing. For inverse powers the derivative
6/L−13/(L−h)<0. The remaining prefactors in the loss also decrease.
The checker verifies the resulting normalized loss is <74 at 169,
while the main excess beyond 1+14/L+60/L², multiplied by L²,
is at least 85−K/L⁷>74. In particular R∼x²/L⁶ under A
and the pointwise formula shows its first correction terms
14/L and 145/L² in this normalization.

## Source locators and verification status

* A: /task/INPUT_CONTRACT.json, A-D02, PsiMajorant.
* CH2 (2512.15709v1): Cor 1.3, original PDF p.3; proof original
  p.36, including the weighted sum and Lemma 9.2 (original pp.35–36).
  The latter has source-computed extrema; only the conservative
  −.751 lower bound on [10^4,10^13] is used.
* Platt–Trudgian finite RH (2004.09765v1): Thm 1, Cor 1, original
  PDF pp.1,4. Cited, not independently re-verified.
* FKS (2204.02588v3): Thm 3.2 and parameter row, original p.8,
  Lem 2.1 pp.4–5, Remark 2.2, Cor 2.3 and Table 1 p.5,
  Cor 1.4 p.2. Used at their original trust status.
* Dusart (2018): Thm 2.3 PDF p.5 (printed p.231), Thm 4.2 PDF p.11
  (printed p.237), Cor 4.5 and its proof PDF p.13 (printed p.239),
  Thms 5.6–5.7 PDF pp.17–18, Thm 5.9 PDF pp.19–20.
* Platt–Trudgian prime-counting (1809.03134v2): Thm 2 PDF p.3.
  The lower finite interval is its literal claim; use only its integer restriction, with the real endpoint corrected above. Dudek–Platt
  (1407.1901v1) Thm 1.2 (PDF p.2) earlier e^9658 baseline.
* Mertens results and finite/ray proof: mertens.md. Codes:
  ray_check.py and mertens_check.py; no formal kernel claim. The
  fixed numerical estimates are executable rational/integer
  certificates (ordinary certificate checking, not source-first PV).
  No numerical observation is used as a hypothesis. The source
  analytic and literature-backed computational premises above
  remain exactly at their admitted levels.

**Arithmetic of the region checker.** For exponentials of z≥0 take
m=max(1,ceil z); at z/m∈[0,1] truncate at degree 30, tail at most
2/31!, round outwards to rational units of 10^−80, then perform
m outward-rounded positive multiplications. Use reciprocals for negatives.
The π bracket uses π/4=4 arctan(1/5)−arctan(1/239) by tangent addition,
and the alternating arctangent series. Other logarithms are enclosed
by the same integer-interval routine as the finite Mertens certificate.
