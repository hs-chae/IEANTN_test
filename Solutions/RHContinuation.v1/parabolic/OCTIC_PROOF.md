# An octic count/width frontier and a2.15 prime-rich interval

This is new post-lock continuation work, with written full-domain analytic proofs,
exact rational continuous numerical certificates, and conditional actual-prime
Lean consumers. The written analytic and scalar-geometric contracts remain
explicit inputs to those consumers. This is not source-first PV or a completed
RH-only Lean proof.

## Two precise results

With RH and the same classical integrated explicit formula and zero-count
inputs as QUARTIC_PROOF.md, for every realu>=exp24,

    #{p prime:u<p<u+2.15*sqrt(u)*log(u)}
      >(9001/9000+5.8/log(u))*sqrt(u).

The ordinary prime-count difference has the same lower bound. Its normalized
liminf is at least9001/9000>1. At width2.16 the same argument gives coefficient
1.009 in place of9001/9000, with the same5.8/logu bonus.

There is a reusable full frontier: for every real1.03<=C<=16 andu>=exp24,

    #{p prime:u<p<u+C*sqrt(u)*log(u)}
      >[(8/9)C-.911+4.2/log(u)]*sqrt(u).

This supports many population targets, not just existence. AtC2.43 its
asymptotic coefficient is1.249; atC4 it is2.644555...; atC16 it is13.311111....
The known published existence coefficients remain substantially better than
what this family supplies for one prime. No uniform domination or global
best-known/optimality claim is made.

## Kernel and rigorous numerical enclosures

Useg(s)=1-s^8 on[-1,1], zero elsewhere. It has peak1 and mass16/9.
Its even Fourier transform is

    f(y)=-16cosy/y²+112siny/y³+672cosy/y⁴-3360siny/y⁵
         -13440cosy/y⁶+40320siny/y⁷+80640cosy/y⁸-80640siny/y⁹,
    f(0)=16/9.

Differentiating gives

    f'(y)=16siny/y²+144cosy/y³-1008siny/y⁴-6048cosy/y⁵
          +30240siny/y⁶+120960cosy/y⁷-362880siny/y⁸
          -725760cosy/y⁹+725760siny/y^10.

The integral definition implies|f|<=16/9,
f>=16/9-(8/33)y², and|f'|<=(16/33)y.
Split at6, integrate these small-y bounds and the termwise absolute derivative
and function tails. The exact upper expressions prove

    int|f'|<18, int|f'|log^+y<34, int_1^infty|f|/y<4.

`octic_quadrature.py` evaluates200,000 directed midpoint cells of width.001
on[0,200], with256-bit dyadic arithmetic and Taylor/angle-doubling resets every
1000cells. Its rigorous midpoint errors are(h/2)*18 for the mass and
(h/2)*(34+4) for the positive log-moment. On[0,1] the missing log contribution
has upper bound-16/9+8/297, because logy is negative and the displayed lower
bound forf is positive there.

For the mass tail retain oscillation in the leading term rather than taking
|cos|<=1. The function|cosy| has periodpi and mean2/pi. Its zero-mean primitive
Q(y)=int_0^y(|cost|-2/pi)dt is periodic and has|Q|<=1. Indeed on a first
half-wave bothsin(theta) and2theta/pi lie in[0,1]; on the second half-wave
both2-sin(theta) and2theta/pi lie in[1,2]. Stieltjes integration by parts gives

    int_H^infty |cosy|/y²dy <=2/(pi*H)+2/H².

Multiply this by16, and use ordinary power tails for the remaining terms.
The log-moment tail can use ordinary absolute power bounds throughout.
The accepted upper expressions are

    A=(1/pi)int_0^infty|f| <1.821020233<1.822,
    B=(1/pi)int_0^infty|f|logy <1.492194727<1.5.

Every lower/upper row in the numerical receipt encloses a calculated rigorous
UPPER-BOUND EXPRESSION. Its lower endpoint is not a lower bound for the actual
moment; only its upper endpoint is used to boundA orB.

## The zero estimate and source domain

Exactly the same distributional/zero-count argument as the quartic yields

    sum_rho delta*|f(delta*gamma)|
      <=1.822log(1/(2*pi*delta))+1.5
       +2delta[14/9+18(1+.28log(1/delta))+.28*34].

The boundary constant14/9 equals(7/8)f(0); both ordinate signs and zero
multiplicity are included. The classical absence of nontrivial real zeros is
used as in the frozen NL proof: the alternating eta series is positive for
0<s<1, andzeta(s)=eta(s)/(1-2^(1-s)) is therefore nonzero. The zero-count
bound impliesN(12)=0 for positive ordinates. No gamma=0 term is discarded by
assuming RH alone, and no unverified table or spacing hypothesis is inserted.

ForD=C*L/2-1, delta=D exp(-L/2), a=exp(L-delta), b=exp(L+delta),
the weighted dpsi main term is at least(16/9)D. AtRH the zero multiplier
is exactlyexp(i*gamma*L)*delta*f(delta*gamma), because the test is
`t^(-1/2)g(log(t/x)/delta)`. The test vanishes at both endpoints. Pairing
against the locally uniformly absolutely convergent integrated explicit formula
includes the endpoint derivative jumps and gives an absolutely summable zero
series. The negative trivial contribution and nonprime prime-power cost are
bounded exactly as in the quartic proof.

## The fixed2.15 coefficient

ForC=2.15 andL>=24, delta<1/6000, the zero-count discrepancy is<.024,
the nonprime cost<.0155 and the trivial cost<.001, with total<.041.
Therefore the ordinary-prime weighted sum is greater than

    (16/9)D-1.822[L/2-log(2*pi*D)]-1.5-.041
      =(9001/9000)L+1.822log(2*pi*D)-(16/9+1.5+.041)
      >(9001/9000)L+5.8.

The last inequality is checked exactly atL24; D increases thereafter.
Divide by the maximum actual prime weightlog(a)/sqrt(a), which decreases
afterexp2. This gives the displayed count at lower endpointa.
The width ratio is at most(C-2/L)(1+4delta), strictly belowC because
4CLdelta<2; exact endpoint gates are in octic_scalars.py.
The continuous strictly increasing mapL->L-delta covers everylogu>=24.
This proves the fixed2.15 theorem on the whole real ray with strict endpoints.
AtC2.16 the main slope becomes1.009 and the logarithmic margin increases,
so the stated2.16 version follows without a new numerical computation.

## The full C family

Uniformly for1.03<=C<=16 andL>=24,

    delta <=8L exp(-L/2)<=192exp(-12)<1/800,
    zero discrepancy <.15,
    nonprime prime-power cost <.058,
    trivial cost <.001.

For the prime-power bound useexp(delta/2)<1.0006,L+delta<1.001L,K<2L,
which gives the explicit upper expression

    1.0006*1.001*L exp(-L/2)*[16.0096L+log(2L)]<.058.

The endpoint check is at24; bothL²exp(-L/2) andLlog(2L)exp(-L/2) decrease
on this ray. The zero discrepancy is a positive increasing function ofdelta
through the permitted range, so its exact maximum is bounded at the displayed
cap. The totalcost is<.21. At the minimum C1.03 andL24,

    1.822log(2*pi*D)-(16/9+1.5+.21)>4.2.

This logarithmic margin increases with bothC andL. The resulting main slope
islambda(C)=(8/9)C-.911, positive throughout the stated C range.
Thus the actual weighted ordinary-prime sum exceedslambda(C)L+4.2.

For the forward conversion the same three elementary factors give

    width/[sqrt(a)log(a)] <=(C-2/L)(1+4delta)
       <C-2/L+4Cdelta <C,

because4CLdelta <=4*16*24*(192exp(-12))<2 at the largest C/smallest L,
andL²exp(-L/2) decreases. The center map is continuous increasing for every
fixedC in the range and covers all logu>=24. This proves the full family.
No sampled grid in C or L substitutes for these monotonicity reductions.

## Why this can improve a published count template

The normalized Fourier convention in Chirre--Pereira--deLaat,
arXiv:2005.02393v3,§1.1(1.2)--(1.3) and§1.3, gives the published sufficient
asymptotic coefficients. Their§3 following(3.9) bounds an in-window Fourier
weight using||F||1. Our compact physical g has actual peak1, massm and
FourierL1 normA. Retaining these separately gives

    sufficient count-width: C>(A+2alpha)/m,

rather than replacing the peak byA and producing(1+2alpha)A/m for this same
kernel. This is a mechanism explanation for the inspected proof passage,
not a claim that those authors never considered any other information.
Their optimized existence constant0.8358 and generic count template remain
in the comparison frontier, especially at low count targets. No conclusion
about their unknown optimum follows from beating a displayed numerical example.

## Exact formal status

EvenKernel.lean is one reusable formal contract/consumer for every even degree,
not a separate architecture for every program. It proves peak bounds, kernel
mass, the main cosh lower bound, finite prime-weight/count conversion and the
actual ordinary prime-count whole-ray consumer. OcticConsumer.lean instantiates
it for2.15 and for the full C family. The explicit formula with multiplicity
and summability, actual zero-density bound, actual prime-power/trivial costs,
and scalar/continuous coverage remain precise parameters. Numeric scripts and
written proofs support them at their stated tier; they are not silently
promoted into RH-only Lean results or source-firstPV.

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
