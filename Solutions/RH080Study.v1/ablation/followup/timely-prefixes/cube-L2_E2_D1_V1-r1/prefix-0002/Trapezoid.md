# Log-trapezoid improvement: finite-threshold cube density without Schoenfeld

**Statements (written source-conditional proof with exact rational certificate; not
formalized in Lean, not independently audited, not source-first PV).**

* Under ordinary RH and the inherited general Green explicit formula and BPT
  zero-counting predicates, for all real n >= exp(8),
  N(n³,(n+1)³) > .8591 n²/log n.
* Under those same inputs, for all real n >= 2154433,
  N(n³,(n+1)³) > .9855 n²/log n.
* Adding the finite Büthe predicate, the .9855 result holds for all real
  n >= 1920, hence in particular from the inherited onset exp(8). Neither
  Nicolas nor Schoenfeld is used in this argument. Keeping Nicolas among the
  assumptions, the .8591 row is also a same-package improvement.

The source propositions are the actual
`RHOcticPush.GreenSource.SourceGreenSmooth` and
`RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate` from
/representation/source/OcticGreenSource.lean and OcticBPTSourceEndpoint.lean.
The former corresponds to Green, *The Prime Number Theorem*, Definition 7.1
and Theorem 7.1, printed p.40 (Mellin decay lemma 7.1, pp.43–44, eqs.7.8–7.11).
The latter corresponds to Brent–Platt–Trudgian, *The mean square of the error
term in the prime number theorem*, JNT 238 (2022), Corollary 1 p.743,
arXiv:2008.06140v1 PDF p.4. These exact inherited interfaces are used; no
new Green or BPT formula is assumed. The closed-count extension from off
ordinates is `publishedBound_of_offOrdinate` in that file. Counts are with
multiplicity. The all-zero decomposition under RH and multiplicity-one
trivial zeros are the inherited `decomposition` and `trivial_multiplicity`
in OcticZeroDecomposition.lean; conjugation and real-axis exclusion are in
OcticZeroPairing.lean (we use the ordinary real-axis nonvanishing of zeta
in the strip, not a numerical test of it).

## 1. General smooth source to strict-open weighted sum

Put x=n³, y=(n+1)³, a=log x, b=log y, H=b−a=3 log(1+1/n).
For a positive integer K let h=HK/(K+1), delta=H/(K+1). Let
g = 1_[a,a+h] * (1_[0,delta]/delta), with convolution in the log coordinate.
This is continuous, lies in [0,1], vanishes at a,b and outside [a,b],
and has integral h. Approximate it by smooth convolutions with
nonnegative integral-one mollifiers supported on [−epsilon,epsilon].
Write g_epsilon for these convolutions. Apply the Green input at X=2 to
the function W(t)=sqrt(x/(2t))*g_epsilon(log(2t)) on t>0 and zero
otherwise. It is smooth compactly supported in [1,infinity) for small
epsilon because x>2. In its source packet substitute w=log(2t):
the packet divided by the zero multiplicity is exactly
(sqrt xint g_epsilon(w)exp((s-1/2)w),dw).
The pole term is (sqrt xint g_epsilon(w)exp(w/2),dw).

For s=1/2+i gamma, on letting epsilon tend to zero the magnitude before
the factor sqrt(x) is exactly h f_K(gamma/T), where T=2/h and
(f_K(u)=|operatorname{sinc}(u)operatorname{sinc}(u/K)|),
(operatorname{sinc}(u)=sin u/u) with its continuous value 1 at zero.
This follows by direct integration of each rectangle and the convolution
identity; the phase cancels in absolute value. The mollifier multiplies
each critical packet by a transform bounded by 1 and converging to 1.
The majorant (f_K(u)lemin(1,K/u^2)) is summable over zeros by BPT
((N(t)=O(tlog t)) and partial summation); count both signs by
conjugation. For the trivial packets uniform summability follows by
using w>=a−epsilon and support length H+2epsilon, giving a geometric
majorant in m for s=−2m. The pole integral converges uniformly on a fixed
compact support. The left side is a sum over a fixed finite set of
integers and converges termwise. At the limit the endpoint weights are
zero (also if x or y is a prime power). Thus there is no hidden
right-closed convention.

The limit pole term is at least x h since w>=a on support.
The total trivial magnitude is at most H/(x²−1), as summing
(sqrt x e^{(-2m-1/2)w}le x^{-2m}) over m≥1 gives
(1/(x^2-1)). For each prime strictly inside (x,y), its weighted
contribution is at most log y since g<=1 and sqrt(x/p)<=1.
It follows that
[
N(x,y)log y ge xh-sqrt x,2hsum_{gamma>0} f_K(gamma/T)
                  - H/(x^2-1)-P ,
]
where P is the sum of log p over nonprime powers (p^m) strictly in
(x,y), m>=2. Multiplicities are incorporated in the gamma sum.

Here and below (L=log n, L_+=log(n+1)). For m=2 there are at most
((3/2)sqrt{n+1}+1) possible integers p by the mean value theorem, each
of weight <=(3/2)L_+. For m>=3 the length in p is
((n+1)^{3/m}-n^{3/m}le1) and hence there are at most two possible
integers per m, each of weight <=L_+. There are fewer than (5L_+)
such exponents because (mle 3 L_+/log 2<5L_+).
With n>=2980 and L>=8, use (L_+le1.001 L) and
(sqrt{n+1}le 1.001sqrt n). Thus (P/(3n^2)le
2L/n^{3/2}+4L^2/n^2) (each of the two exponent cases is
bounded by the corresponding term). Also
(H/(3n^2(x^2-1))le1/(3n^5)), by (Hle3/n, n^6-1ge3n^2).
These bounds overestimate the normalized losses since
(L/log yle1/3). The main normalized term
(xh L/(n^2log y) = (K/(K+1))nlog(1+1/n)L/L_+)
is bounded below by
[
rac K{K+1}rac{n}{n+1}rac{1}{1+1/(nL)}
]
using (1/(n+1)lelog(1+1/n)le1/n), by integrating (1/t).
For a scalar cap (Z) on (2hsum_{gamma>0}f_K(gamma/T)),
the normalized nontrivial loss is at most (Z/(3sqrt n)).

## 2. Exact enclosure of the weighted positive-ordinate sum

Use BPT in the form
[
N(t)=rac{t}{2pi}(log(t/(2pi))-1)+7/8+R(t),
qquad |R(t)|le .28log tquad(tge2pi).
]
Set (u_j=pi j/M); first index j0 is chosen to satisfy (u_{j0}ge1).
Since (Tge 2n/3), all frequencies at or above (Tu_{j0}) are safely
in the BPT domain. For (0<gammale Tu_{j0}) use bound 1.
Use cells ((Tu_j,Tu_{j+1}]) from j0 through J−1 with rational
majorants (m_j) for (f_K) (construction below). For (gamma>Tu_J)
use (K(gamma/T)^{-2}). All three parts are disjoint and exhaustive.

The contribution to Z from the smooth RvM term is at most
[
 2(j_0/M)(log T+log(j_0/(2M))-1)
 + (2/M)sum_{j=j_0}^{J-1}m_j(log T+log((j+1)/(2M)))
 + rac{2K}{pi u_J}(log T+log(J/(2M))+1).
]
Include (2h(7/8)) from the low-frequency count in addition to this formula.
Indeed the leading low-frequency count uses (2hT=4). On cells,
upper bound the integral of (log(Tu/(2pi))) by its right-endpoint
value times width (differentiate the RvM main). The tail integral against
the smooth density is exact, by integrating (log(Tu/(2pi))/u^2).
The constant 7/8 cancels in differences and has no derivative. We
absorb the low-frequency constant by using the remainder with 7/8
retained as described below.

For the low part and finite cells, the coefficient of (R(Tu_j))
is (1-m_{j_0}) at j0, (m_{j-1}-m_j) at subsequent nodes and
(m_{J-1}) at J, multiplied by (2h). This discrete partial summation
is valid even if (Tu_j) is a zero ordinate. The tail BPT residual
in absolute value is bounded by
[
 2h, .28 (K/u_J^2)(2log(Tu_J)+1/2)
]
by integration by parts on ((Tu_J,infty)). One boundary residual
costs (log(Tu_J)); the density integral uses
(2int_{u_J}^{infty}log(Tu)u^{-3}du
=(log(Tu_J)+1/2)/u_J^2).
In particular, since (log(Tu_J)ge1/2), a cap on the combined
BPT residuals is (2h, .28, log(Tu_J)V), where
[
 V=|1-m_{j_0}|+sum_{j_0<j<J}|m_j-m_{j-1}|
      +m_{J-1}+3K/u_J^2.
]
The extra low-frequency (2h(7/8)) is at most (21/(4n)), using
(hle3/n); it is independent of the cell residual and is included
as a separate term in the certificate. Nothing is assumed about
individual ordinate locations.

**Cell calculation.** Bound pi between 3.14159 and 3.14160.
Evaluate the two absolute sine factors at the midpoint in units of
pi, reduce its rational angle by symmetry and periodicity to [0,pi/2],
and bound the sine by its degree-9 alternating Taylor upper sum.
Use the upper pi in positive terms and lower pi in negative terms.
Each reduced sine is bounded above by 1 as well. Across the cell use the
global Lipschitz constant 1 for sin and |sin|, so add pi_hi/(2M)
and pi_hi/(2MK) to the respective midpoint upper bounds. Divide by
the lower endpoint enclosure of u (respectively u/K), bound each
factor by 1, multiply and round upwards to units of 10^−10.
This proves the individual continuum cell bounds. The low term and
remaining tail bound bridge the entire frequency line, not just a
finite sample.

The script uses only integer and rational arithmetic in all tests.
For log(a) reduce a>0 to 2^v r with 1<=r<=2. For r use
(2sum_{j=0}^{11}z^{2j+1}/(2j+1)) with (z=(r-1)/(r+1))
and remainder between 0 and (2z^{25}/(25(1-z^2))).
Use the lower cap on log 2 if v<0. Decimal lines printed after tests
are not used as proof inputs.

## 3. Whole rays and constants

For (nge a_0) and (L=log n), the certificate checks a strict
rational upper bound (d) for (log(2(K+1)(a_0+1)/(3Ka_0))).
So (log Tle L+d). Substituting upper logs in the smooth sum, using
(pige3.14159) in the nonnegative tail, yields a cap (A L+B).
Replacing (log(Tu_J)) by (L+C) as in the code, the final cap is
[
Zle A L+B+rac{42}{25}rac{(L+C)V}{n}+rac{21}{4n}.
]
Using (2hle6/n) explains 42/25. The scalar cap on the normalized
error is largest at the ray onset (alpha):
((A L+B)e^{-L/2}) decreases for (Lgelogalpha) because
(A(logalpha-2)+Bge0); the certificate verifies the last inequality
with a lower bound on (logalpha). Likewise ((L+C)n^{-3/2}),
(n^{-3/2}), (L n^{-3/2}), (L^2n^{-2}), (n^{-5}) decrease.
The rational main term lower bound is increasing in n and L.
Use the lower bound (a_0lealpha), lower/upper bounds for
(logalpha), and lower bound for (sqrtalpha) shown below.

| alpha | a_0 | log alpha bounds | sqrt alpha lower | K,M,J |
|---|---:|---|---|---|
| exp(8) | 2980 | 8,8 | 54.598 | 32,64,16384 |
| 2154433 | 2154433 | 14.58,14.583039 | 1467.798 | 480,96,196608 |

The exponential and logarithm comparisons and rational Machin check
on pi are supplied by `scalar_checks.py`.
The two final strict rational comparisons, with loss terms included,
are .8591 and .9855. The finite bridge to 1920 follows from §2 of
candidate.md: ((19/30+26/(25cdot1920))/sqrt{1920}<.0145)
and (2154434^3<10^{19}).

Reproduce: `/usr/bin/python3.10 /work/submission/sinc_certificate.py`.
This script is an exact arithmetic implementation of the displayed
bounds, not evidence of a verified C/Lean program path for this method.
