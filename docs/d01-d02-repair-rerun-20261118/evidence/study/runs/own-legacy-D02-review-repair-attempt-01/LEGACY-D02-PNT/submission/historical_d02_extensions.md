# Further improvements and tertiary applications

This file adds two supported arguments to candidate.md and mertens.md.
Use extra_check.py with Python 3.10 (-B avoids creating any cache).
The original paper statements keep their original computation status.

## Ramanujan even without the input assumption

Unconditionally, in the sense of no hypothesis A or full RH (admitted
finite-height computations retained),
\`\`\`
R(x)>0.03 x²/L⁶       for all real L=log x≥2840,
R(x)>0.004 x²/L⁶      for all real 169≤L≤753.
\`\`\`
Together with candidate.md, the unconditional lower positive piece
goes up to exp(753), with the corrected sharp left endpoint and the
admitted original *integer* finite interval. This does not bridge the
unconditional gap 753<L<2840. The upper ray improves e^3915 to e^2840
under the *same* assumptions as the original large ray and adds a
strict quantitative lower bound on their common domain.
The pointwise two-sided expression from candidate.md is also
unconditional on L≥2840 if E is replaced by the smaller of E_C and
the explicit bound for E_U below.

There is also a source-independent-of-the-low-integer-check
margin R(x)>0.1 x²/L⁶ on 37.5≤L≤39.45, without A. This uses the
same original finite RH and Dusart inputs, not the Platt–Trudgian
low integer Ramanujan interval. Since θ(t)<t up to 1.39·10^17
and exp(39.45) is smaller than that, the upper (one-sided) error
for the normalized π−Li₂ is at most 3L exp(−L) by partial
summation. Use this in the squared term, and still use E_RH
for the lower bound of π(x/e). The geometric-ratio proof of r
works from L=36 (indeed 4/(1−16/L)≤2L there), and the same
coefficient calculation for D uses 36 instead of 38 in the
sum defining the K-tail. The rational covering with cells of
width 0.01 verifies the .1 lower margin. This recognizes the
asymmetry of the two π factors without presuming a sign
on the continuation beyond the proven θ<x range.

**New unconditional theta estimate.** For every real v≥λ=2834,
\`\`\`
|θ(e^v)/e^v−1| ≤ K/v⁴,       K=0.321.
\`\`\`
Use R₀=5.573412 from Dusart Thm 2.4 (PDF p.5; see also Feb-independent
FKS discussion §1, Remark 1.5). In this section only, R₀ is the
zero-free-region constant, not the prime-counting gap. Put c=0.9926,
z=log H₀ with H₀=3·10^12. For λ≤v≤4000 use FKS Thm 3.2 at
T=e^54, with T⋆<e^55. Its parameter constraints hold on this entire
interval (log x≤4000<e^54 and 5e^54+2<e^(λ/2)).
Multiplicities are included. Split the zero sum at .9 and c:

* Below .9 the truncated reciprocal sum is <500 by the FKS bound
  used in candidate.md (v there replaced in the height estimate by
  log T⋆<55).
* Between .9 and c use B(s) of candidate.md. For .9≤s≤c,
  the same derivative formula gives B(s)≤B(c)e^(95(c−s)); the
  constants in extra_check.py verify this using the lower endpoint .9.
  The layer integral gives at most B(c) v/(v−95)e^(−(1−c)v).
* At β≥c use finite RH, the zero-free region, and
  2∫_(H₀)^∞ w_v(t)dN(c,t) where
  w_v(t)=exp(−v/(R₀ log t))/t. The weight is decreasing on this
  range because v≤4000<R₀z². Integration by parts has no
  boundary term at H₀ or infinity (N(c,H₀)=0, and use Dusart's
  sublinear density bound at infinity). After log t=u, the upper
  bound is the following nonnegative integral:
\`\`\`
I(v) = ∫_z^∞ [9.8·3^p u^q exp((p−1)u) + 103 u² exp(−u)]
              exp(−v/(R₀u)) (1−v/(R₀u²)) du,
p=(8/3)(1−c), q=5−2c.
\`\`\`
  This bound uses both the height-dependent zero-free cap and the
  density in a *single* decreasing height weight, avoiding a loss from
  treating these bounds separately.

The part u≤80 in v⁴I(v) is largest at λ: λ>4R₀·80, so v⁴
times the exponential decreases, and the last factor also decreases
and is nonnegative. In the integral at λ replace z by 28.729<z,
and use u^q≤1.07u³ up to 80. Upper rectangles of width ≤.01 using
positive factor-wise rational intervals explicitly cover [28.729,80].
For u≥80 discard the zero-free factors, use u^q≤u⁴, and bound
u^k≤80^k exp(k(u−80)/80), k=4 or 2. The tail integral is then a
pair of elementary decreasing exponentials. The code bounds this tail
times 4000⁴ and the truncation by 2.091·4000⁵ e^−54.
The low and middle contributions times v⁴ decrease on [λ,4000].
Cor 4.5 adds ≤3e^(−v/2) to the relative psi error. Taken together,
the explicit bounds total <K after scaling by v⁴. For v≥4000
the FKS Cor 1.4 bound plus 3e^(−v/2) works directly. The scaled
terms are decreasing there, and at 4000 their sum is <K, as checked.

For L≥λ+5, in the partial summation integral for π use the CH2
bound below v=L/2, and above L/2 use
K/v⁴ + a₀·1_(v<λ) +117exp(−v/2) for the relative theta error.
For the K term the log derivative of exp(v)/v⁶ is ≥1−12/L.
For the a₀ prefix term and the square-root term above L/2 use
v^−2≤4/L². We get the explicit error
\`\`\`
L⁴ E_U(L) =
  K + K/(L−12) +4 a₀ L³ exp(λ−L)
  +(9/4)L⁵[a₀ exp(−L/2)+234 exp(−3L/4)]
  +(936 L³+117 L⁴) exp(−L/2) +3 L⁵ exp(−L).
\`\`\`
Here the equals defines E_U. The bound plus L⁴r(L) decreases there.
At L=λ+5 it is <.322. Thus for L≥2840 the loss scaled by L⁴
is at most .322[(L/(L−1))^5+2+4/L+.322/L⁴].
The added K-tail in the polynomial comparison (different K:
the 1276000000 constant from candidate.md) is harmless, and the
checker verifies that the total is <.97. This proves the upper
unconditional ray with margin .03. The intermediate interval
is certified in cells of width .5 with E_C and the same polynomial
comparison, no FKS use required there.

## Oscillation-aware Mertens transfer under A

For L≥200, define s₀=.77, a=5/32, b=27/32,
\`\`\`
A₀(L)=.119 L/(L−97),
dθ(L)=d_A(L)+3 exp(−L/2),
B_Y(s)=9.8·3^p Y^(p−1) (log Y)^q/(1−p−q/log Y)
              +103(log Y)²/[Y(1−2/log Y)],
             p=(8/3)(1−s), q=5−2s,
r_A(L)=.02 L² exp(−.23L)+2.091 L exp(−L/3)+3 exp(−L/2)
                   +exp(−a L) B_(exp(L/3))(s₀),
A₂(L)=2.51·10^(−14) L/(L−97),
W(L)=w₃(L)+|w₃′(L)|/a,  w₃(L)=(1+L)/L².
\`\`\`
See candidate.md for d_A. With u=(θ(x)−x)/x, use
\`\`\`
|δV − u|      ≤ e^(−aL) A₂(L) + r_A(L)/a,
|δS − u/L|    ≤ W(L)e^(−aL) A₂(L) + w₃(L) r_A(L)/a.
\`\`\`
Thus obtain an explicit Mertens envelope using |u|≤dθ(L), adding
1/(2 floor x) for δQ and using the exact exponential conversion.
Alternatively use the observed boundary u with these certified
residuals for a signed interval. Simple uniform corollary, under A:
\`\`\`
max{both product relative errors, |δS|} ≤ .24 x^(−5/32)/log x,
|δV| ≤ .24 x^(−5/32),                           x≥e^200.
\`\`\`
This is strictly better throughout this common domain than the
original .2/L³ and .3/L² (also than the improved unconditional
coefficient-only envelopes), since .24 L²e^(−aL) decreases and
is already <.125 at 200. The more exact envelope has limiting
coefficient at most .119+2.51·10^(−14) in these scalings.
It improves the factor 1+1/a that results if the oscillatory
tail is bounded only by the pointwise absolute majorant.
Take the minimum with the other valid bounds.

**Proof.** The density argument applies at any lower height Y≥H₀:
2Σ_(γ≥Y,β≥s)1/γ ≤ B_Y(s), by integrating 2N(s,t)/t²
over t≥Y (zeros below Y make only an extra nonnegative contribution).
The high-zero series
g(v)=−2 Re Σ_(γ>0,β≥s₀) exp((ρ−1)v)/ρ
is absolutely convergent by that density bound. Extend the high
part of FKS Thm 3.2 to this infinite series; its missing high
tail from γ>T⋆≥e^(v/3) is bounded by exp(−a v)B_(exp(v/3))(s₀).
The low part, truncation and prime-power difference are the other
three terms of r_A. Therefore |Δ(e^v)/e^v−g(v)|≤r_A(v).
The coefficient exp(a v)r_A(v) decreases on v≥200; for B_Y the
first numerator's log-derivative in z=log Y is p−1+q/z<0
and its denominator increases, similarly for the second term.
This proves the remainder integral bounds r_A(L)/a and
w₃(L)r_A(L)/a.

For the spectral integral the same derivation with 2/γ² instead of
2/γ uses 4∫_H₀^∞N(s,t)/t³ dt, giving
\`\`\`
B₂(s)=19.6·3^p H₀^(p−2) z^q/(2−p−q/z)
       +206 z²/[H₀²(2−2/z)].
\`\`\`
Here B₂ is the density weight, not the constant B₃ in δV.
The negative logarithmic derivative of its first term is bounded
above by the same 97 (larger denominator); B₂(b)<2.51·10^−14
is checked. Layer integration as before yields
2Σ_(γ>0,β≥s₀) exp((β−1)L)/γ² ≤ A₂(L)e^(−aL).
Termwise integration is justified by absolute domination of the
series on the ray and the integrable exponential common envelope.
Integrating exp((ρ−1)v) gives the extra denominator ρ−1 whose
absolute value exceeds γ; this proves the first improved bound.
For w₃ integrate by parts once and use |w₃′(v)|≤|w₃′(L)| and
exp((β−1)v)≤exp((β−1)L)exp(−a(v−L)); this gives the W factor.
The checker also uses the coarser 2w₃(L) and A₀/H₀, valid by the
same integration by parts and ∫|w₃′|=w₃(L), to certify the simple
.24 coefficient. All scaled bounds in that calculation decrease,
so checking at 200 suffices. In particular the r_A coefficient
tends to zero. No claim is made about the sign of the log error.

## Tertiary: improved primorial normalization and prime intervals

Let n_x=∏_(p≤x) p. Under A, for x≥e^200, Euler's elementary
product for φ(n_x) (counting by inclusion-exclusion) and log n_x=θ(x)
yield
\`\`\`
| log[(n_x/φ(n_x))/(exp(γ) log log n_x)] |
   ≤ W(L)e^(−aL) A₂(L) + w₃(L)r_A(L)/a
      +1/(2 floor x) + 2 dθ(L)²/L .
\`\`\`
In particular
\`\`\`
| (n_x/φ(n_x))/(exp(γ) log log n_x) −1 | ≤ .0069 x^(−a)/L
\`\`\`
on the entire stated ray, and the limsup of L x^a times this
absolute relative error is at most 2.51·10^−14. The boundary u/L
cancels: the log error equals
δQ−log(1+log(1+u)/L). For |u|≤dθ(L)<1/2, the difference between
u/L and this subtracted logarithm is at most
u²/L+4u²/L²≤2u²/L, using the log series twice. The scaled
right-hand side used for the uniform coefficient decreases for L≥200
and the checker verifies it at 200 (including conversion from log).
This is a magnitude bound, **not** a proof of a one-sided sign
criterion on primorials.

For every x≥e^200 there is a prime in (x,x+0.465 x^b], and
\`\`\`
π(x+0.465 x^b)−π(x) > 0.000999 x^b/(L+.1).
\`\`\`
More precisely, let C(L)=e^(aL)dθ(L). For any
h > 2 C(L) x^b/[1−b C(L)x^(−a)] the interval (x,x+h] has a prime.
Indeed C is decreasing and C(200)<.232. Subtract the errors
at x+h and x in θ and use (x+h)^b≤x^b+b h x^(b−1) by concavity.
For h=.465 x^b the resulting θ excess beats .000999 x^b while
log(x+h)<L+.1; the lower bound on the prime count follows.
In particular consecutive prime gaps after a prime ≥e^200 have
this bound and for every η>0 the length (0.238+η)x^b works
on a sufficiently large ray. In comparison, a direct conversion of
A plus Cor 4.5 would use a variable length on the order of
x^b log² x, with a coefficient already >1000 at log x=200 when
using the two endpoint bounds. No optimum for prime gaps is claimed.
