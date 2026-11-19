# Ramanujan gap: exact endpoint and quantitative ray
Let L=log x, d=5/32, beta=27/32, A=1/64, q=1048/10^15. The first route below assumes A-D02 for its high branch. The extended result, at the end, also gives an unconditional-at-admitted-trust optimal positive ray. Let H(u)=sum_{j=0}^{20} j!/u^j,
V(u)=4u exp(-u)+12*21!/u^21, and c=397888/10^7.
Define normalized F(u)=u*pi(exp u)/exp u. For u>=35.98 put
h0(u)=q+117 exp(-u/2), h1(u)=A*u^2 exp(-d*u)+3 exp(-u/2).
For u>=40 put
  m0(u)=q*20/(19u)+117 exp(-u/2)*20/(9u)+(16/5)u exp(20-u).
For u>=220 put
  m1(u)=A*u exp(-d*u)/beta + (20/3) exp(-u/2)/u
            +(u/220)exp(220-u)*m0(220).
Let E(u) be the minimum of available bounds: c*u^2 exp(-u/2) for u<=58,
h0+m0 for u>=40, h1+m1 for u>=220. Write E+(u)=0 if u<=43 and E(u) otherwise.
For every L>=36.98,
  F(u) in [H(u)-E(u), H(u)+V(u)+E+(u)]   (u=L-1,L).
In particular the real-ray two-sided certificate is
  L/(L-1)*(H(L-1)-E(L-1)) - (H(L)+V(L)+E+(L))^2
  <= R(x)*L^2/x^2
  <= L/(L-1)*(H(L-1)+V(L-1)+E+(L-1)) - (H(L)-E(L))^2.
Direct bound or quantitative corollaries below can be used independently.

## Derivation
li is the principal-value integral from zero (not the integral offset at 2).
At u=24, 0 < li(exp 24)-exp(24)*H(24)/24 < 4 (rational
certificate in analytic.py). The derivative of exp(u)*H(u)/u is
(exp(u)/u)*(1-21!/u^21). For u>=24,
(d/du)(exp(u)/u^22) >= (1/12)*exp(u)/u^22.
Integrating the positive residual yields
H(u)<= u*li(exp u)/exp u <= H(u)+V(u).
The finite-RH Corollary 1 in PlattTrudgianFiniteRH.pdf p.4 supplies the
bounds at u<=58 and lower that are used here; p.5 §3.3 quotes the
literature-backed π< li on [2,10^19], hence up to exp(43).
CH2 Corollary 1.3 gives q+113.67 exp(-u/2) for the relative psi error;
Dusart Corollary 4.5 adds <3 exp(-u/2) for all u>=0, so h0 controls
the relative theta error. The same correction and A-D02 imply h1 from
u>=200. Write e_theta(u)=(theta(exp u)-exp u)/exp u.
Partial summation gives
  F(u)-u*li(exp u)/exp u = e_theta(u)+u exp(-u)
      *(C + integral_40^u e^v e_theta(v)/v^2 dv).
At u=40 the two finite-RH bounds are each <64 exp(-20), so |C| <=(16/5)exp(20).
For alpha in {1,1/2}, (exp(alpha*v)/v^2)' >= (alpha-1/20)*exp(alpha*v)/v^2
on v>=40. Thus the integral plus anchor, multiplied by u exp(-u), costs
at most m0(u). Alternatively split at 220, where the same accumulated
part costs m0(220), not h0(220)+m0(220); integrating h1 beyond 220 costs
the first two terms in m1. This proves the brackets by monotonicity of
the square on the positive arguments (positivity also follows from elementary
bounds on E). All π,θ jumps are inclusive.

## Initial certified corollaries
R(x)>0.00002*x^2/L^6 for L>=36.98; R(x)>(1+13/L)*x^2/L^6 for
L>=48. The finite-interval tests and infinite-tail comparisons are supplied
in analytic.py. The positivity window [10^11,1.15*10^16] is Dudek–Platt
Lemma 3.4 (PDF p.10), a literature-backed computation independent of RH.
Its upper endpoint exceeds exp(36.98). We use our independently run
bridge.cpp certificate for [38358837683,10^11] rather than relying on
a real endpoint issue in Platt–Trudgian Thm.2.

## Exact lower endpoint
Let a=1644673232, b=632207037. The point r is the unique root
e*r*b/log r = a^2 in (38358837682.217,38358837682.219).
On the entire [38358837682,38358837683], both prime counts are a,b:
the first interval's right endpoint is composite, and floor(x/e) is
14111427770 throughout. The combinatorial count certificate and rigorous
root bracket are given with the other arithmetic tests. Thus R(x)>0 for
every x>r under the stated assumptions, and NO real-ray onset strictly
below r is possible. For integer x the optimal start is 38358837683.
The source's literal positive open interval after 38358837682 is incompatible
with this local check: R remains negative immediately to the right of that
integer. Its other ray from exp(3915) is retained unconditionally. This
endpoint correction is not an improvement over the erroneous real endpoint in
isolation; the new result closes the huge unchecked transition and locates the
actual final zero, with a positive margin on the principal analytic ray.

## Extended result: positivity at the optimal onset without A-D02
Use the smoothed pointwise ψ bound from smoothing.md. For u>=40, add
Dusart's prime-power correction (<3 exp(-u/2)) and absorb 2 exp(-u)
into the low term. The relative θ error is bounded by
123 exp(-u/2)+3.6e-6 exp(-δu/2). The same partial summation proof as
above, with anchor at 40, gives a further normalized π error bound
  ESδ(u)=123 exp(-u/2)(1+20/(9u))
       +3.6e-6 exp(-δu/2)(1+1/(u(19/20−δ/2)))
       +(16/5)u exp(20-u).
Take E as the minimum of all available bounds, omitting h1+m1 if A-D02
is not invoked. Use δ=1/8 without A-D02 at the trust of the admitted
OpenAIQRH Theorem 1.1, or δ=5/32 with A-D02. The same bracket as
above holds for L>=36.98.

Numerically certified simple consequences:
* Without A-D02, **R(x)>0 for every real x>r**, where r is the final
  zero in (38358837682.217,38358837682.219), as defined above.
* Without A-D02, R(x)> (1+12/L)*x²/L^6 for L>=48.
* With A-D02, R(x)> (1+13.9/L)*x²/L^6 for L>=48.

In the unconditional proof, neither the interval between 36.98 and 48
nor any of the lower-range arithmetic uses the contract. The exact
threshold follows by linking the local root, the new finite bridge,
the admitted DP Lemma 3.4, the rational finite-real-interval certificate
from L=36.98, and the smoothed analytic ray. No infinite-RH assumption
is made. In particular exp(3915) can be replaced by the exact open
threshold r even without A-D02 under the permitted original theorems.
At r itself R(r)=0, so the closed ray cannot begin there.

For the margin checks, let S_k be the coefficients of H(L)^2 as a
polynomial in 1/L. The coefficients of L/(L−1)*H(L−1) through k=20
are b_k=sum_{j<=k} binom(k,j) j!, by positive binomial series.
Thus the normalized main gap, times L^4, has lower bound
  sum_{k=4}^{20}(b_k−S_k)L^(4−k) − sum_{k=21}^{40}S_k L^(4−k).
The coefficients at k=4,5,6 are 1,14,145; those at 7..20 are positive.
analytic.py and mcheck.py replace each positive decreasing power by
its value at the right endpoint of each closed rational bin, and
negative terms by their left endpoints, with upward error estimates
for the costs E,E⁺,V. When checking 1+n/L they first combine 14/L
and −n/L. For L>=300, the rescaled high-degree negative tail is
absorbed by 145/L², and L^5 times the error cost based on ESδ
is decreasing termwise below 14−n at 300. This proves the margins
on the full rays, not just at mesh points.
