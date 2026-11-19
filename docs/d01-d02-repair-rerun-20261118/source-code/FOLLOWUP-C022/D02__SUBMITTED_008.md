# Mertens products and prime sums — unconditional and A-dependent results

Use the real-variable conventions in candidate.md. Let
\`\`\`
δQ = log Q(x) − γ − log L,         L=log x
δS = Σ_{p≤x}1/p − log L − M
δV = Σ_{p≤x}(log p)/p − L + B₃.
\`\`\`
The relative errors for P,Q are respectively |exp(−δQ)−1| and
|exp(δQ)−1|. In particular their maximum is exactly exp(|δQ|)−1.

## U. A strictly improved unconditional envelope (finite frontier + analytic ray)

All entries with units c/10^6 in mertens_results.txt define bounds
on whole real rays starting **at** the listed onset (inclusive).
Column 0 bounds both product relative errors by c/(10^6 L³),
column 1 bounds |δS| by c/(10^6 L³), and column 2 bounds |δV|
by c/(10^6 L²). Use the minimum of all applicable entries. In addition:
* Both product errors are ≤0.199999/L³ for x≥2278382; |δS| is
  ≤0.199999/L³ for x≥2278383. These are strict improvements throughout
  the original rays of Dusart 5.9 and 5.6 with no change of assumptions.
* For example, both are bounded by 0.125/L³ for x≥7126757, uniformly
  37.5% smaller than the original 0.2 coefficient; and the product
  errors are ≤0.3/L³ already for x≥624908. The weaker coefficient
  buys a significantly larger domain, and is not claimed to dominate
  Dusart on its intersection. Taking minima restores both benefits.
* For the weighted sum, the stronger 0.135/L² holds for x≥7126757
  and 0.22/L² for x≥2275976. The strict refinement 0.2999995/L²
  holds for the entire original x≥912560 ray. The more aggressive
  0.299999/L² is actually false at x=912560, as also checked.

## U-sharp. Exact smallest real onset for the original 0.2 product envelope

Let N*=2278382, C=e^(−γ)Q(N*), and x* be the unique solution in
(N*−1,N*) of (log x*)²(C−log x*)=1/5. Then the simultaneous
0.2/L³ product bounds hold for every real x≥x*, and **no strictly smaller
real onset** works. The certificate brackets x* by
\`\`\`
2278381.711141839 < x* < 2278381.711141843.
\`\`\`
No prime jumps on [N*−1,N*] (including N* composite), and throughout
that interval 0<log(C/log x)<.01 by the log certificate and monotonicity.
Thus the maximum of the two errors, scaled by L³, is L²(C−L).
Its derivative in L is L(2C−3L)<0. Opposite signs at the bracket
endpoints give the unique root, and points arbitrarily close below the
root violate the threshold. On [N*,∞) use either U or Dusart Thm 5.9.
This improves the **real** onset, not the first admissible integer,
and identifies the sharp onset only for the given coefficient 0.2.

**Prime-sum benchmark onsets, also sharp as real numbers.**
For |δS|≤.2/L³ the earliest ray starts at the unique root x_S of
L³δS=.2 in (2278382,2278383). For |δV|≤.3/L² it starts at the
unique root x_V of L²δV=.3 in (912559,912560). The exact solver
gives the strict brackets
\`\`\`
2278382.1129 < x_S < 2278382.1130,
 912559.9973 < x_V <  912559.9974.
\`\`\`
In each closed unit interval the right endpoint is composite and the
prime sum is constant, with any prime at the left already included.
The signed centered residual is positive over that interval and the
scaled error strictly decreases (see derivative check below).
Certified signs at the brackets show a violation arbitrarily close
below the root. From the next integer onward use U (or the original
Dusart Thm 5.6 or 5.7). These are exact onset characterizations,
not a claim about the best coefficient on a fixed large ray.

## Explicit analytic envelope, with or without A

For v≥log(10^8), define a nonnegative bound d_U(v) on |θ(e^v)/e^v−1|:
\`\`\`
d_U(v)=
   1.751000147 exp(−v/2)+1.78 exp(−2v/3)     (v<29.9)
   (v²/25) exp(−v/2)                        (29.9≤v≤58)
   a₀+117 exp(−v/2)                         (58<v<3000)
   min{a₀+117 exp(−v/2), 9.22022 v^(3/2) exp(−.8476836√v)+3 exp(−v/2)}
                                             (3000≤v).
\`\`\`
The first piece uses the lower bound ψ−x>−.751√x from CH2 Lemma 9.2
on 10^4≤x≤10^13, Dusart Cor 4.5, and θ(x)<x in this range.
The second uses Finite RH Cor 1. The other two use CH2, FKS Cor 1.4
and Dusart Cor 4.5. For A, use d(v)=min{d_U(v),0.284 exp(−a v)+117 exp(−v/2)}
throughout, and from v=160 include in that minimum d_A(v)+3 exp(−v/2).
Without A simply use d=d_U. Values at junctions can be replaced by
the smaller bound when both pieces apply (this does not affect integrals).

For j=3,2, take respectively weights w₃(v)=(1+v)/v², w₂(v)=1,
boundary bounds b₃=d(L)/L, b₂=d(L), and tail integrals
T_j(s)=∫_s^∞ d(v)w_j(v)dv. An explicit signed interval for δS (j=3)
and δV (j=2), for every x≥10^8:
\`\`\`
[l_j,u_j]=
  [−b_j−T_j(39), T_j(L)]               for L≤39,
  [−b_j−T_j(L), b_j+T_j(L)]             for L>39.
\`\`\`
For δQ use [l₃−1/(2 floor x),u₃]. Thus the normalized product factors
are in [exp(l₃−1/(2 floor x)),exp(u₃)] for Q and the inverse interval
for P. A common symmetric bound is exp(max(|l₃−1/(2 floor x)|,|u₃|))−1.
Take the minimum with U. These formulas are exact convergent integrals
of elementary explicit functions; evaluation by interval quadrature is
not required for validity. The sign saving at L≤39 is from θ<t for
t<1.39·10^17 (Dusart Cor 4.5 proof), hence the two summands up to 39
have opposite signs. See the exact Mertens identities in candidate.md.

**Whole-ray strict comparator.** Even without A the displayed analytic
signed intervals imply product errors <0.125/L³, |δS|<0.125/L³,
|δV|<0.135/L² on x≥10^8. This is checked by ray_check.py, with
rational enclosures on intervals covering the *entire* finite region
and monotone majorants on the infinite one. Details:
* At L≥3000 the FKS branch is <0.0003/L³: at 3000 use the rational
  certificate, then L^(9/2) exp(−.8476836√L) and
  L³ exp(−L/2) decrease. The tail T₂ contributed by v≥3000
  is bounded by 0.0003/(2·3000²). On [58,3000] integrate a₀+117e^(−v/2).
  Multiplying boundary plus tail by L² bounds the constant
  terms at 3000 and the decaying exponential at 58.
  For w₃ use T₃≤w₃(L)T₂ and b₃=b₂/L.
* At 29.9≤L≤58 the full triangle bound is used.
  Extending the exponential piece to infinity in the tail is safe
  if the upper bound for the tail above 58 is added. The two
  exponential integrals are (2L²+8L+16)e^(−L/2)/25 and
  (2L+6)e^(−L/2)/25 respectively. Times L² or L³, the relevant
  low-end polynomials times e^(−L/2) decrease from 29.9.
* On 18.42≤L≤29.9, the first analytic piece is used only above log(10^8).
  For d(v)=k e^(−f v), T₂≤k e^(−f L)/f for that piece.
  Write I_m=∫_L^∞ e^(−f v)/v^m dv. Integration by parts gives
  I₁+I₂=e^(−fL)/(fL)+(1−1/f)I₂. At f=1/2 use
  I₂≥ e^(−fL)/(fL²)(1−2/(fL)), from integration by parts and
  I₃≤e^(−fL)/(fL³). At f=2/3 discard the negative multiple of I₂.
  This gives the expressions in the checker, adding the later tail as
  an absolute constant. 2/L−2/L²+8/L³ decreases there. For the
  negative endpoint use the boundary and only the tail beyond 39.
  The floor-tail is at most e^(−L). For log-to-relative conversion
  use exp(z)−1≤z/(1−z), 0≤z<1, from the exponential series.

## Verification of the finite envelope and the sharp real onset

mertens_check.py is a standalone Python 3.10 exact-integer certificate.
The sieve erases multiples starting at each surviving p². Every
composite ≤10^8 has a least prime factor ≤√(10^8), so all and only
primes survive. No supplied prime table is used.
There are 236784 closed cells in [10000,10^8]. On a cell [a,b],
each uncentered sum and log Q is nondecreasing, so bracket it
between the ordinary inclusive endpoint values; then subtract the
smooth baseline bracket. The resulting errors are multiplied by
the relevant powers of log b and rounded outwards. A failure at
coefficient c makes b a new candidate onset. Since the terminal
cell is certified at the reported coefficients and the analytic ray
is valid starting at 10^8, this procedure proves the whole ray.

Some cells use a sharper **constant-prime-state** guard (including
both pre- and post-jump values at each prime, and both exterior
endpoints). For the product write C=e^(−γ)Q for this state's normalizer.
The signed functions L²(C−L) and L³(L/C−1) have derivatives
L(2C−3L) and L²(4L/C−3). If the starting point passes the threshold
(all guards have c≤3 and L>9), C/L<4/3, which remains true as L
increases over that constant-prime-state piece. Hence the two
functions are respectively decreasing and increasing. For the
reciprocal sum, derivative of L³(S−M−log L) has sign of
3(S−M−log L)−1, negative at the start and thereafter. For the log
weighted sum, derivative of L²(V+B₃−L) has sign of 2(V+B₃−L)−L,
again negative. Taking also their negatives justifies exact
endpoint checking, not grid extrapolation.

All arithmetic uses exact integers in units B=2^80. For log z with
1≤z≤2 use 2Σ(v^(2j+1)/(2j+1)), v=(z−1)/(z+1), starting with floor
units; the next-power error is <4 units by the recursion in lp.
Division of a power by its odd denominator has error <5 units.
The omitted Taylor tail in B units is <1 for 26 terms at v≤1/3.
For 5 terms use the range-reduced mantissa table j/256, giving
v<1/512 with tail again <1. Thus 261 and 51 unit error allowances.
Floor/ceil accumulation for 1/p, log p/p, and log p/[p(p−1)]
uses these one-sided rational enclosures. For the correction
−log(1−1/p)−1/p, use the exact log interval for p<1024, otherwise
terms 2..6 and tail ≤1/(7p^6(p−1)).

Gamma is enclosed without a decimal input. Let A(t)=t/2−t²/12+t⁴/120.
For t=1/k define
r(t)=log(1+t)−t/(1+t)−A(t)+A(t/(1+t)).
Then r(0)=0 and
r′(t)=−t⁶(t²+5t+5)/[30(1+t)^5].
Hence −t⁷/10<r(t)≤0 on [0,1]. Sum over k≥n, using the
telescoping definition of γ and
Σ_{k≥n}k^(−7)≤n^(−7)+n^(−6)/6. This gives
0≤γ−(H_n−log n−A(1/n))<1/(30n^6) for n≥6.

For the M and B₃ constants in the finite computation N=10^8.
The analytic pieces above give |θ(t)−t|≤t/5000 for all t≥N;
the boundary checks are in ray_check.py. For a positive decreasing
test kernel f with tf(t)→0 and convergent integral, tail partial
summation bounds |Σ_{p>N}log p f(p)−∫_N^∞ f(t)dt| by
[2Nf(N)+∫_N^∞ f(t)dt]/5000. Apply to
f(t)=1/[t(t−1)] for B₃ (integral is log(N/(N−1)));
for M use f(t)=1/[2t²log t], accounting for the remaining
k≥3 by ≤1/(3N²), since 1/[3t²(t−1)]≤2/(3t³).
Its integral is I₁(log N)/2 with f-exponent 1 in I₁;
repeating integration by parts gives alternating bounds after
12 and 13 terms. This is why the constant intervals in the output
are sharper than bounding tails over all integers. It is not a
circular use of Mertens bounds.
