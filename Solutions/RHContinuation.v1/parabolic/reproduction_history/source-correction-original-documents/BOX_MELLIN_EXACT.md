# Exact first box moment and a128-log certificate for the second

New continuation mathematics. The exact identities below have independent
coordinator first-pass review, but remain analytic contracts in Lean. The finite
Python computations are exact directed rational arithmetic, not source-first PV.
The later C-source component is separately proved and connected below. This
replaces the box's128000-cell oscillatory computation by128logarithms, while
strengthening the resulting moment and actual-psi envelope.

## An exact regularized absolute Mellin transform

Writephi(y)=siny/y, and

    H(s)=int_0^infty |siny| y^(s-2)dy  (0<s<1).

Its simple pole ats=0 has residue1. The constant and linear coefficients are
exactlyJ0,J1 from PsiSmoothing.J, because subtracting1_{y<=1} leaves an integral
that and its first derivative are dominated locally uniformly for|s|<1/2.
Nearzero use|phi-1|<=y²/6; at infinity use|phi|<=1/y.

The elementary uniformly convergent Fourier series is

    |siny|=(4/pi) sum_{n>=1}(1-cos(2ny))/(4n²-1).

Its coefficients follow by integrating siny*cos(2ny) on[0,pi]. The constant
coefficient uses sum1/(4n²-1)=1/2. Every summand1-cos is nonnegative, so
Tonelli is applicable before any expansion. The standard positive Laplace/gamma
integral gives

    int_0^infty(1-cosy)y^(s-2)dy=pi/[2Gamma(2-s)cos(pi*s/2)].

It follows that

    H(s)=P(s)[zeta(1+s)+sum_{k>=1}4^(-k)zeta(2k+1+s)],
    P(s)=2^(-s)/[Gamma(2-s)cos(pi*s/2)].

The geometric expansion of1/(4n²-1) is positive and absolutely convergent;
its derivative in s is dominated uniformly near0 by a convergent logn/n³
series. Thus all summations and coefficient extractions used here are justified.

Letgamma be Euler's constant andgamma1 the first Stieltjes constant, with
zeta(1+s)=1/s+gamma-gamma1*s+O(s²). Putaa=1-gamma-log2. Gamma recurrence and
the usual Gamma expansion at1 give

    P(s)=1+aa*s+[aa²+1+pi²/12]*s²/2+O(s³).

The constant additional zeta series has an elementary exact evaluation:

    sum_{k>=1}4^(-k)zeta(2k+1)
      =sum_{n>=1}1/[n(4n²-1)]
      =lim_N[H_(2N)+H_(2N+1)-2H_N-1]=2log2-1,

using1/[n(4n²-1)]=1/(2n-1)+1/(2n+1)-1/n.
Therefore the first actual absolute regularized moment is EXACTLY

    J0=log2.

No numerical integration or individual zero data is needed for this identity.
The derivative of the zeta series is

    sum_{k>=1}4^(-k)zeta'(2k+1)
      =-sum_{n>=1}logn/[n(4n²-1)].

Thus the second actual moment is

    J1=-gamma1-sum_{n>=1}logn/[n(4n²-1)]
        +aa*log2-aa²/2+1/2+pi²/24.

The first Stieltjes coefficient also has the convergent Euler-sum formula

    gamma1=lim_N S_N,
    S_N=sum_{n<=N}logn/n-(logN)²/2.

It follows by differentiating the locally uniform Euler-summation remainder
forzeta(1+s)-1/s: its truncated remainder and derivative are uniformly
O(N^(-1+|s|)*(1+logN)) for|s|<1/2. This supplies the Laurent coefficient
rather than treating an unrelated limit as an automatic zeta identity.

## Two independently reproducible finite upper bounds

ForN>=3 the decreasing functionf(t)=logt/t gives by rectangle comparison

    S_N-logN/N <=gamma1<=S_N.

UsingN4096, truncating the positive q-sum after4096 and applying exact Euler
gamma harmonic bounds at1024 gives

    J1 <.709698029 <.710.

This accepted fallback takes4096directed logarithms and no sine/cosine calls.
Its actual source and receipt are box_mellin_series.py andbox-series-normal.json.

A stronger and much cheaper inequality follows from convexity. For t>=5,

    f''(t)=(2logt-3)/t³>0.

On every unit interval a convex function's trapezoid lies above its integral.
ForM>N>=5, writingE_NM for the nonnegative sum of these trapezoid errors,

    S_M-S_N=E_NM-f(N)/2+f(M)/2.

TakeM to infinity, usingf(M)->0. This proves

    gamma1>=S_N-logN/(2N).

No unexplained Euler--Maclaurin remainder constant is needed. WithN128 the
finite rigorous upper expression is

    U128=-S_128+log128/256
       -sum_{2<=n<=128}logn/[n(4n²-1)]
       +aa*log2-aa²/2+1/2+pi²/24.

Since the omitted q terms are positive, J1<=U128. The actual directed program
box_mellin_trapezoid.py uses256-bit dyadic arithmetic, the exact log atanh
series with remainder, Machin pi and Euler gamma bounds at1024. It proves

    U128 <.708742712 <.70875=567/800.

This is an enclosure of an UPPER-BOUND EXPRESSION; its lower endpoint is not
an actual lower bound onJ1. The reported0.925s is one observed native wall
measurement, not a causal performance experiment. The earlier box quadrature
has128000cells and one observed45.43s run, while the new method has128logterms.
All raw commands/resources and successful normal/-O/-OO runs are retained;
no speedup is inferred solely from the differing counts of arithmetic steps.

## Stronger actual-psi function and mathematical consumers

Substitute these moment bounds into the same box zero-density and averaging
argument from BOX_PNT_PROOF.md. For every realx>=exp35, L=logx,v=L/2-logL,

    |psi(x)-x| <=sqrtx *
      {[v²+2log2*v+1.4175+L]/(2pi)+.14}.

The previous analytic and numerical allowances are retained; no new zero
assumption, RH verification height or computational prime table is introduced.
The full function is uniformly stronger than the frozen B5 profile. The
intermediate4k/.710 consumer already has a kernel-checked>.546 comparison
against B5, hence the sharper128/.70875 version inherits that comparison.
The actual average, zeta multiplicity packet and continuous real domain are
those in PsiSmoothing, not a formal polynomial pretending to bepsi.

## Completed source-first C numerical component

The unchanged executable C source `verified_finite_log.c` is now reused on all
127 nontrivial integer inputs2..128. Its existing source-byte/AST, UInt64/UInt128
arithmetic, source-closed helper calls, loops and termination proofs are rebuilt
from source. CLogMathLower and CLogSource prove a true two-sided log enclosure:
returned/2^40−2^-30 <= logn <= returned/2^40 on the exact new domain. The lower
bound comes from the positive20-term atanh polynomial and a kernel check of the
actual integer algorithm, not subtraction of an assumed error guess. Every
native C returned word is separately matched to that source-proved model.

CLogMoment consumes these source-derived intervals and proves a rational upper
expression approximately.708744640424<567/800. EulerLower unconditionally proves
its accelerated actual-gamma harmonic lower bound; qTerm_summable proves the
positive omitted series converges. CLogMomentNetwork.box_moments connects the
result to the actual existing IEANTN moment conclusion. Its box_psi theorem
composes that numerical leaf into the actual canonical PNT conclusion without
any numerical-moment premise. The final replay also compiles the canonical
RHSmoothingInputs.v1.challenge_box_moments solution wrapper.

The remaining analytic inputs are precise: actual first-moment integrability
and J0=log2; actual second-moment integrability and the exact Mellin coefficient
identity; actual Stieltjes-sequence convergence and its128-term trapezoid bound.
They are the three none-yet conclusions of BoxMellinInputs.v1. The actual-PNT
consumer additionally retains the averaged explicit formula and actual zero-sum
density estimate. Main/trivial estimates are discharged by PsiElementary.

This is source-first PV of the C logarithm component followed by kernel
aggregation and conditional analytic consumers. It does not verify the Python
harness or the entire Mellin analysis. Correct restricted-C/GNU-C semantics,
GCC compilation, integer ABI, runtime, OS, hardware and the build/run association
remain the documented platform boundary. The full source and trust chain is
recorded in README.md and CLAIMS_AND_GAPS.json.

Primary zero-count input: Brent--Platt--Trudgian, Accurate estimation of sums over zeros of the Riemann zeta-function, Corollary1, publishedp743 (arXiv2008.06140v1 PDFp4), https://arxiv.org/pdf/2008.06140v1#page=4. It centersN(T) atT/(2pi)log(T/(2pi e))+7/8 and gives|R(T)|<=.28logT forT>=2pi. The opposite sign printed locally in Lee--Nosalv4 Eq8 is a historical source typo already audited; it is not the contract used here. The integrated formula is Dudek--Grenie--Molteni arXiv1503.05403v2 PDFp2, https://arxiv.org/pdf/1503.05403v2#page=2.
