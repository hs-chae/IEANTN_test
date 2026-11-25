# Strict-open cube population: matched onset and earlier tradeoffs

All variables n are **real** unless explicitly stated. Write
`D_c(n)` for `N(n³,(n+1)³) > c n²/log n`, with both endpoints excluded.
The statements below distinguish the inherited assumption package from
alternative published analytic/computational inputs. No result here establishes RH.

| Result | Range | Assumptions | Proof status |
|---|---|---|---|
| D_0.781 | n ≥ exp(8) | unchanged inherited RH+Green+Nicolas+BPT, via its octic family | written derivation, §1 |
| D_0.7433 | n ≥ exp(8) | ordinary RH + Schoenfeld source predicate, no Büthe | written derivation, §2 |
| D_0.96699 | n ≥ 400 (in particular the matched exp(8) range) | ordinary RH + Schoenfeld + Büthe source predicates, **replaces** octic package | written derivation, §2 |
| D_0.988 | exp(8) ≤ n ≤ 2154433 | Büthe finite source predicate only | written derivation, §2 |
| D_0.792 | 12 ≤ n ≤ 2154433 | Büthe finite source predicate only | written derivation, §2 |

A written derivation is not labelled independently audited. The strict-open
theta transfer in §2 is Lean kernel checked in `ThetaTransfer.lean`; the first
transfer receipt lists only propext, Classical.choice and Quot.sound.
Published source predicates are tier B, not new axioms. The compiled compact
dual numerical obstruction is a distinct D result; the assigned V1 C-source
proof pertains to that selected compact-dual scalar model, **not** these
counts or the historical Büthe computation.

## 1. Same-package improvement by exact adaptive cell widths

Use the octic family in /task/COMMON_FACTS.md (the actual baseline source
declaration is `RHOcticPush.OptimizedFinal.strict_count_family` in
/representation/source/OcticOptimizedCertified.lean). Let
(L=\log n), (L_+=\log(n+1)), (s=\sqrt n/L), and (x=n^3, y=(n+1)^3).
The interval of length (3n^2) starting at (x) lies inside the cube
up to its left endpoint. Set (k=\lceil 1.001s/16ceil) and (H=3n^2/k).
Use all (k) open cells ((u,u+H)) with (u=x+iH), (0\le i<k).
Use the **exact** cell parameter (C_u=H/(\sqrt u\log u)).

Here are uniform geometric bounds. For (n\ge e^8), (n>2980),
(L\ge8), (L_+\le L+1/n\le 1.000042L). For (0\le r\le1/12),
((1+r)^3\le(1+8r/5)^2): after cancelling (r\ge0), the difference
is (1/5-(11/25)r-r^2\ge0). Thus
(\sqrt y\le(1+1.6/n)n\sqrt n\le1.00054n\sqrt n).
In particular (\sqrt u\log u\le1.001\,(3n\sqrt n L)), whereas it is
at least (3n\sqrt n L). Consequently
(s/(1.001k)\le C_u\le s/k\le16).
For (k=1), (s\ge e^4/8>6.82); for (k\ge2),
(1.001s/16>1) and (k<1.001s/8), giving (C_u>8/(1.001)^2).
The lower admissibility threshold (1.03) is met, and (u\ge e^{24}).
The bound on (s) uses the increase of (e^{L/2}/L) for (L>2).

Write (b=.91015,d=1.3999,S=1.00054,U=1.000042). The normalized
contribution of all cells exceeds
[
  (8/9)/U - (k/s)S(b-d/L).
]
Indeed each main term is exactly ((8/9)H/\log u), and the subtracted
term is ((b-4.2/\log u)\sqrt u) with
(0<b-4.2/\log u\le b-d/L), as (dU<1.4).
All open cells are disjoint; excluding their internal boundary primes can
only decrease the sum of the counts, so it is a legitimate lower bound
for the strict-open count.

* (k=1): ((bL-d)e^{-L/2}) decreases for (L\ge8) by differentiation.
  Bound loss by (S(8b-d)/54.598), using (e^4>54.598).
* (k\ge2, s\le24): (L<12) because (e^6/12>24) and (s) increases.
  Bound loss by (1.001S(b-d/12)/8).
* (s>24, k\ge2): use loss at most (Sb(1.001/16+1/24)).

In each case the displayed rational lower coefficient exceeds .781,
independently of any optimizer or sample. (e^4>54.598) follows by
summing the exponential series through degree 20; (e^6>288) follows
through degree 7. The cube theorem is strictly stronger than the matched
.70 density at every n on the same domain and under the same package.
This also exceeds the baseline's other cube-frontier branch:
((5.08985+1.4/L)/s\le(5.08985+.175)/(54.598/8)<.781).

## 2. Endpoint-safe Chebyshev method

Let `theta(z)` be the sum of log p for primes p ≤ z and `thetaLeft(y)`
the sum for p < y. The latter is the eventually constant left-limit of
theta (finite primes below y). For x ≥ 0 and y > x,
[
  N(x,y)\log y \ge 	heta(y^-)-	heta(x).
]
This includes removal of the lower endpoint even when x is prime, and
costs no upper-endpoint error: use the left-limit of the *lower* analytic
bound at y. The upper bound at x is strict and remains strict in the
difference. With (E(z)=\sqrt z(\log z-2)\log z/(8\pi)) the two transfers are:
[
 N(x,y)\log y > y-x-E(x)-E(y)\quad (x\ge 2300000000);
]
[
 N(x,y)\log y >y-x-1.95\sqrt y+.05\sqrt x
   \quad(1423\le x<y\le10^{19}).
]
The former uses RH; the latter uses only Büthe including the indicated
strict one-sided sign. No rounding of x or y appears in either transfer.

For Schoenfeld, take x=n³ and y=(n+1)³, (L=\log n\ge8).
The normalized main term ((y-x)L/(n²\log y)\) is at least 1:
(y-x\ge3n^2(1+1/n)) and (L_+\le L+1/n\le L(1+1/n)).
Bound (E(x)+E(y)\le(\sqrt x+\sqrt y)(\log y-2)\log y/(8\pi)).
The simple bound ((1+r)^{3/2}\le1+2r) for (0\le r\le1), with r=1/n,
gives a normalized error at most
[
 R(L,n)=(1+1/n)L(3L-2+3/n)/(4\pi\sqrt n).
]
For (n\ge a\ge2\) and (L_a=\log a\ge8), (R(L,n)\le R(L_a,a)).
To see this, replace the occurrences of 1/n by 1/a, write (v=L-L_a\),
and use \(\sqrt n\ge\sqrt a(1+v/2+v^2/8)\). For
(P(t)=t(3t-2+3/a)) one has (P(L_a)/2\ge P'(L_a)\),
(P(L_a)/8\ge3), so (P(L_a+v)\le P(L_a)(1+v/2+v^2/8)\).
The source domain is satisfied on both rays in the table.
For (a=e^8) use (a>2980,\sqrt a>54.598,L_a=8).
For (a=2154433) use (8<L_a<14.583039,\sqrt a>1467.798).
Using \(\pi>3.14159\), the resulting rational caps on R are strictly
less than .2567 and .03301, respectively. The upper log bound at the
seam is verified by the degree-52 Taylor lower bound on exp(14.583039).

For Büthe, if (n\ge a\ge12), (y\le10^{19}), then (x\ge1423).
Use the same main-term bound (valid for (L\ge1)) and
((1+1/n)^{3/2}\le1+1.6/n), as in §1.
As (L/\log y\le 1/3), the normalized error is at most
[
 (19/30+26/(25a))/\sqrt a.
]
At (a=12,400,e^8) this is strictly less than .208, .03301, .012,
respectively. The hybrid seam overlaps: (2154434^3<10^{19}).
This table does not treat any observation from a grid at a finite x as
a uniform proof.

## Source identity notes

Schoenfeld, *Math. Comp.* 30 (1976), Theorem 10 (6.1), printed p.337
(PDF p.1), DOI 10.1090/S0025-5718-1976-0457374-X. The local
/corpus/literature/Schoenfeld1976.pdf currently hashes to
8c3cac1ee52eb05af05ec410adc587a18505a46aacdde41ae097038b0e7c3897,
the recovered primary according to SCHOENFELD_PRIMARY_PIN_ADDENDUM.json,
not the quarantined 57-page publisher response. The OCR line 34 is garbled;
use the domain and constants from the exact task predicate.

Büthe, arXiv:1511.02032v2 (22 Oct 2017), Theorem 2 (1.6), (1.7),
PDF p.2, DOI 10.1090/mcom/3264. Local Buthe1511.02032v2.pdf SHA-256
350f96313810ded3e8eaf2af6006b227c8834235e177f49eabb3d43d4931c4d1.

## Active follow-up

Development beyond this checkpoint: sharper fixed-onset explicit-formula
smoothing, exact finite early onsets, and formal tail/finite scalar
inequalities. CMS and Blanquer Robles comparisons must respect the finite
or asymptotic ranges, and the compact dual does not constrain macroscopic
cube density.
