# The sextic continuation improves the direct prime-rich coefficient to2.18

New continuation result; written full-domain proof with exact rational continuous
Fourier certificates. No original experimental arm is credited with this result.
Analytic formalization and source-first PV remain separate from the numerical
and conditional kernel-checked consumers.

Assume RH and the same classical integrated explicit formula and positive-
ordinate zero-count theorem as in QUARTIC_PROOF.md. For every realu>=exp24,

    #{p prime:u<p<u+2.18sqrt(u)log(u)}
        >(353/350 +5.6/log(u))*sqrt(u).

In particular the ordinary right-continuous prime-count difference satisfies
the same bound, and its normalized liminf is at least353/350>1.
The open upper endpoint and all-real onset are preserved.

## Kernel and rigorous moment certificate

Replace the quartic by g(s)=1-s^6 on[-1,1], zero elsewhere.
It is nonnegative, has peak1 and mass12/7. Its even Fourier transform is

    f(y)= -12cosy/y²+60siny/y³+240cosy/y⁴
          -720siny/y⁵-1440cosy/y⁶+1440siny/y⁷,
    f(0)=12/7.

Repeated integration by parts or the recurrence for int s^(2m)cos(ys)ds
proves the formula. Differentiating gives

    f'(y)=12siny/y²+84cosy/y³-420siny/y⁴
           -1680cosy/y⁵+5040siny/y⁶+10080cosy/y⁷-10080siny/y⁸.

The integral definition gives|f|<=12/7,
`f(y)>=12/7-(2/9)y²`, and`|f'(y)|<=(4/9)y`.
For largey take absolute values termwise in the displayed formulas.
Splitting at5 proves V=int|f'|<12 andVlog=int|f'|log^+y<23;
W=int_1^infty|f|/y<4. The actual upper expressions are approximately
11.876068,20.313526,3.319110 and are checked by exact rational endpoint gates.

The directed 50,000-cell width.002 quadrature on[0,100], with the same exact
Taylor/interval arithmetic and variation/tail proof as the quartic, proves

    A=(1/pi)int|f| <1.715470235<1.72,
    B=(1/pi)int|f|logy <1.2427925<1.3.

On[0,1], the missing log contribution has upper bound-12/7+2/81.
Tail integrals use the absolute coefficient/power majorants displayed above.
Every interval row in the numerical JSON encloses the computed UPPER-BOUND
EXPRESSION; its lower endpoint is not a lower bound for the actual moment.
Only the upper expression endpoint is used for the actual moment inequality.

## Full zero/prime-power argument

The common Stieltjes argument in QUARTIC_PROOF.md, with f(0)=12/7, gives

    sum_rho delta*|f(delta*gamma)|
      <=1.72log(1/(2*pi*delta))+1.3
         +2delta[3/2+12(1+.28log(1/delta))+.28*23].

The term3/2 is(7/8)f(0); both signs and actual multiplicities are counted.
There is no individual zero computation or reciprocal-zero numerical premise.

For everyL>=24 choose

    x=expL, D=(109/100)L-1, delta=D exp(-L/2),
    a=exp(L-delta), b=exp(L+delta).

The main weighted dpsi integral is at least(12/7)D. The test is
`t^(-1/2)g(log(t/x)/delta)`, so atRH its exact zero transform is
`exp(i*gamma*L)*delta*f(delta*gamma)`, with no imaginary-shift correction.
Summability and endpoint jumps are handled exactly as in the quartic proof.

Here delta decreases and is below(109/100)*24exp(-12)<1/6000.
The displayed zero-count discrepancy is<.017. The common nonprime prime-power
bound is<.0155 and the trivial contribution is<.001, for totalcost<.034.
These constants and all monotonicity signs are checked by sextic_scalars.py.
The logarithmic coefficient remains positive on the whole ray.

Consequently the actual weighted sum over ordinary primes exceeds

    (12/7)D-1.72[L/2-log(2*pi*D)]-1.3-.034
      =(353/350)L+1.72log(2*pi*D)-(12/7+1.3+.034)
      >(353/350)L+5.6.

The final strict bound follows at24 by exact rational logs and then
monotonicity ofD. Divide by the maximum prime weightlog(a)/sqrt(a), proved to
be decreasing fora>exp2, to obtain the desired count at center endpointa.

The relative full width satisfies

    (b-a)/(sqrt(a)log(a))
      <=(2.18-2/L)(1+4delta)
      <2.18-2/L+8.72delta <2.18,

because8.72Ldelta<.04<2 on the whole ray. As before, L->L-delta is
continuous, strictly increasing, starts below24 and tends to infinity.
It covers everylogu>=24, giving the theorem for every realu>=exp24.
The positive asymptotic excess353/350-1 survives asu tends to infinity;
this is stronger than a vanishing5.6/logu excess by itself.

## Exact formal boundary

SexticWindow.prime_count_218 is a compiled actual-primeCounting whole-ray
consumer with explicit decomposition into actual weighted Mangoldt, actual
zeta-zero packet/multiplicity/summability, actual positive prime-power cost,
trivial term and scalar geometric coverage. The raw main integral bound,
finite prime-weight/cardinality conversion and ordinary counting conversion
are proved in Lean. The written analytic/stieltjes and geometric obligations
remain parameters; no one should call the entire theorem RH-only formalized.
The Python directed computation is rigorous numerical support at the stated
continuous-integral tier, not source-firstPV of Python or C source.

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
