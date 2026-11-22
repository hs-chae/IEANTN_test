# A direct quartic-window RH prime-count theorem

This is new continuation work. It does not alter either frozen discovery arm.
The mathematical argument is a written proof using the same precisely stated
integrated explicit formula and zero-count theorem as the frozen NL argument.
The numerical leaves are directed exact-rational continuous-integral enclosures,
not source-first PV and not an end-to-end Lean proof.

## Statement

Assume RH and the classical integrated explicit formula and the zero-count bound
`|N(T)-M(T)| <= .28 log T` for `T>=2*pi`, with
`M(T)=T/(2*pi)*log(T/(2*pi*e))+7/8`, counting positive ordinates with
multiplicity. These last two are published analytic theorems, not extra
conjectures or a numerical table. For every real `u>=exp(24)`,

    #{p prime: u<p<u+2.22*sqrt(u)*log(u)}
      > (1.006 + 5.2/log(u))*sqrt(u).

Consequently the same lower bound holds for
`pi(u+2.22*sqrt(u)*log(u))-pi(u)`, and its normalized liminf is at least
`1.006>1`. The strict open upper endpoint is part of the result.
This strengthens the prior written coefficient2.43/count1+.04/logu at
its entire stated domain, with the same analytic premises. No claim that2.22
is best known or optimal is made without the coordinator's literature review.

## Kernel and independently reproducible numerical leaves

Put `g(s)=1-s^4` on[-1,1], and0 elsewhere. Its peak is1 and mass is8/5.
Its real Fourier transform is even and

    f(y)=int_{-1}^1 g(s)*exp(i*y*s)ds
        = -8*cos(y)/y^2 +24*sin(y)/y^3
          +48*cos(y)/y^4 -48*sin(y)/y^5,  y!=0,
    f(0)=8/5.

Twice integration by parts proves this identity; the removable value at0 is
also the integral definition. The derivative for nonzero y is

    f'(y)=8*sin(y)/y^2 +40*cos(y)/y^3 -120*sin(y)/y^4
           -240*cos(y)/y^5 +240*sin(y)/y^6.

The integral definition gives `|f(y)|<=8/5`,
`f(y)>=8/5-(4/21)y^2`, and `|f'(y)|<=(8/21)y` for y>=0.
For y>=4 the explicit formulas give

    |f(y)| <= 8/y^2+24/y^3+48/y^4+48/y^5,
    |f'(y)| <= 8/y^2+40/y^3+120/y^4+240/y^5+240/y^6.

Splitting at4 therefore proves

    V=int_0^infty |f'| <7.21,
    Vlog=int_0^infty |f'|*log^+(y) <12,
    W=int_1^infty |f|/y <2.7.

For example V is at most64/21+2+1.25+.625+.234375+.046875,
which is7.203869...<7.21. Vlog and W are elementary integrations of the
displayed power/log majorants (verified by `quartic_scalars.py`).

`quartic_quadrature.py` uses 50,000 cells of width.002 on[0,100], exact
256-bit dyadic directed arithmetic, alternating Taylor bounds for the fixed
sine/cosine step and half-step, and interval rotations at every midpoint.
It proves the continuous bounds

    A=(1/pi)*int_0^infty |f(y)|dy <1.54,
    B=(1/pi)*int_0^infty |f(y)|*log(y)dy <.9.

For A add midpoint error `(h/2)V` and analytic tail
`8/H+12/H^2+16/H^3+12/H^4` atH=100.
For B integrate only[1,H] numerically, with upper tangent log values,
add midpoint error `(h/2)(Vlog+W)`, and the corresponding power-log tail.
On[0,1], f is positive and
`f>=8/5-(4/21)y^2`; multiplication by negative logy reverses the order,
so this missing contribution has upper bound `-8/5+4/189`.
The midpoint error bound follows by integrating local variation on each
half-cell: every derivative value is charged length at mosth/2.
These are all-real integral bounds, not sampled estimates.

## Zero-sum estimate

The published count bound at12 givesN(12)=0, so there are no positive
ordinates below12. For allT>0, `R(T)=N(T)-M(T)` obeys
`|R(T)|<=1+.28*log^+(T)`, because below2*pi, N=0 and|M|<1.
AlsoR(0+)=-7/8. Integration by parts against the nonnegative absolutely
continuous function`delta*|f(delta*T)|` gives

    sum_rho delta*|f(delta*gamma)|
      <= A*log(1/(2*pi*delta))+B
         +2*delta*[7/5+V*(1+.28*log(1/delta))+.28*Vlog].

The sum is over both signs and multiplicity. In particular the factor2
in the discrepancy and the boundary value7/5=(7/8)*(8/5) are present.
The M density contribution is exactlyA*log(1/(2*pi*delta))+B.
The derivative majorant is integrable, and the boundary at infinity vanishes.
No unverified individual zero table or reciprocal-zero numerical sum is used.

## Weighted prime powers and finite-range constants

For anyL>=24 put

    x=exp(L), D=(111/100)*L-1,
    delta=D*exp(-L/2), a=x*exp(-delta), b=x*exp(delta).

ThenD>0 andD<2L. The functiondelta decreases, and
`delta <(111/100)*24*exp(-12)<1/6000`.
Also`log(1/(2*pi*delta))>0`: this is true at24, and its derivative is
`1/2 - (111/100)/D >0` throughout.
The discrepancy in the previous display is strictly below.011 on this ray;
the positive function`d*(c-c'logd)` is increasing on0<d<=the stated cap,
so one exact endpoint check suffices.

Pair dpsi with the compact weight

    w(t)=t^(-1/2)*g(log(t/x)/delta).

The integrated explicit formula, integrated twice by parts including the
endpoint derivative jumps, gives the main integral, the displayed zero
sum, and the trivial-zero contribution. At RH the zero term is exactly
`exp(i*gamma*L)*delta*f(delta*gamma)`. This is absolutely summable because
f(y)=O(y^-2); the operation is justified first against the locally uniformly
absolutely convergent integrated formula. The main integral is

    sqrt(x)*delta*int_{-1}^1 exp(delta*s/2)*g(s)ds
      >= (8/5)*sqrt(x)*delta=(8/5)*D.

The negative trivial-zero contribution is less than
`2*delta/[sqrt(a)*(a^2-1)]<.001`. Constant-log terms disappear under dpsi.
The weight vanishes at both endpoints, so prime powers there have zero weight.

The weighted contribution of nonprime prime powers is bounded by

    Q <= exp(delta/2)*(L+delta)/sqrt(x)
         *[2*delta*exp(delta/2)*sqrt(x)+log K],
    K=floor((L+delta)/log2).

Indeed for eachk>=2 count at most1 plus the interval length of possible
integer bases, bound logp by(L+delta)/k and p^(-k/2) by1/sqrta,
then use`sum_{k>=2}1/k^2<=1` and`sum_{k=2}^K1/k<=logK`.
SinceK<2L, delta<=2L*exp(-L/2), exp(delta/2)<1.0002 andL+delta<1.001L,

    Q <=1.0002*1.001*L*exp(-L/2)
           *[4.0008*L+log(2L)] <.0155.

BothL^2 exp(-L/2) andL log(2L)exp(-L/2) decrease forL>=24; the exact
endpoint check is recorded. The sum of discrepancy, prime-power and
trivial costs is strictly below.028.

## Actual prime count and forward coverage

It follows that the weighted sum over ordinary primes is strictly larger than

    (8/5)D -1.54*(L/2-log(2*pi*D))-.9-.028
      =1.006*L +1.54*log(2*pi*D)-2.528
      >1.006*L+5.2.

The last strict inequality is an exact check atL=24 and monotonicity ofD.
Each prime in(a,b) contributes at most`log(a)/sqrt(a)`, becauseg<=1 and
logt/sqrtt decreases fort>exp2. Thus

    #{p:a<p<b} >[1.006*L+5.2]*sqrt(a)/(L-delta)
                   >[1.006+5.2/log(a)]*sqrt(a).

The full width ratio is

    (b-a)/(sqrt(a)*log(a))
       =(2D/L)*exp(delta/2)*(sinh(delta)/delta)/(1-delta/L)
       <=(2.22-2/L)*(1+4delta)
       <2.22-2/L+8.88delta <2.22.

For the elementary factor bound use each of the three factors<=1+delta
and(1+delta)^3<=1+4delta fordelta<=1/4. The final strict inequality
follows from`8.88Ldelta<.04<2`; its left side is bounded at24 since
L^2 exp(-L/2) decreases. Hence(a,b) is contained in the claimed open
forward interval at the lower endpointu=a.

FinallyL->log(a)=L-D exp(-L/2) is continuous, strictly increasing, starts
below24 atL=24 and tends to infinity. Its image covers everylogu>=24.
This proves the stated theorem for every realu>=exp24, with no unexamined
exp24..exp35 gap and no prime-endpoint exception. Taking the normalized
liminf of the proved full-domain pointwise estimate gives>=1.006>1.

## Mathematical inputs still to formalize

The continuous explicit-formula pairing and zero-count Stieltjes integration
are written analytic arguments here. The exact numerical certificate and
scalar endpoint gates are completed separately. A standard-axiom Lean proof
of the algebraic count/endpoint consumer does not by itself formalize those
analytic inputs or verify the Python source program. The coordinator should
retain these tiers separately and independently review this complete proof.

The classical nonvanishing of zeta on the real interval(0,1) is part of the analytic source justification: alternating eta is positive and zeta(s)=eta(s)/(1-2^(1-s)) there. Thus gamma=0 has not been discarded merely fromRH. See the original frozenPNT.md derivation.

Primary zero-count input: Richard P. Brent, David J. Platt and Timothy S.
Trudgian, *The mean square of the error term in the prime number theorem*,
Journal of Number Theory 238 (2022), 740–762, Corollary 1 on published page 743
(arXiv2008.06140v1, PDF page 4),
https://arxiv.org/pdf/2008.06140v1#page=4.
The published author copy is https://maths-people.anu.edu.au/~brent/pd/rpb274-final.pdf#page=4.
It centers N(T) at T/(2*pi)*log(T/(2*pi*e))+7/8 and gives
|R(T)|<=.28logT for T>=2pi, as printed in both primary PDF versions.
The proof-bearing cutoff here is A=12>2pi, so the endpoint T=2pi is not used.
The original non-strict source-domain wording already agrees with the paper;
there is no endpoint mismatch or extra endpoint theorem being claimed. The
opposite sign printed locally in Lee–Nosalv4 Eq8 is a historical source typo
already audited; it is not the contract used here.

This is a different paper from the same authors' *Accurate estimation of sums
over zeros of the Riemann zeta-function*, Mathematics of Computation 90 (2021),
2923–2935 (arXiv2009.13791v1), https://arxiv.org/pdf/2009.13791v1.
The latter's PDF page 2, footnote 1, cites the former's Corollary 1 for A=.28.
The previously combined title/arXiv locator has been corrected; the zero-count
formula and constants used in this proof are unchanged.

The integrated formula is Adrian W. Dudek, Loïc Grenié and Giuseppe Molteni,
*Primes in explicit short intervals on RH*, arXiv1503.05403v2, PDF page 2,
the displayed psi1 formula following the Perron representation:
https://arxiv.org/pdf/1503.05403v2#page=2.

The exact primitive residues, including r=log(2*pi) and the trivial-zero series,
are expanded in BOX_PNT_PROOF.md under “Exact primitive residues and the trivial
term.” Its subsequent averaging argument applies integration by parts before
interchanging the primitive zero series; it does not differentiate that entire
series or infer a derivative from the size bound on R1.
