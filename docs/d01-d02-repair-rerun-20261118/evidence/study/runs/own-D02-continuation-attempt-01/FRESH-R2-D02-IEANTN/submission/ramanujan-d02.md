# Ramanujan gap: new profile portfolio

Keep every valid result of `ramanujan.md`, `gap-results.md` and
`orders.md`; these files describe the reviewed D01 floor, all of
which is already (B_0) here. For (x>1), let (t=log x),
(G(t)=t^6 R(x)/x^2), where (R(x)=(ex/t)pi(x/e)-pi(x)^2).
Bounds for (G) below are strict unless designated otherwise.
They hold for **real** (x), including prime arguments; onsets
and both ends of finite windows are inclusive.

The optimal strict-positivity ray is still (x>r) with the
inherited exact root (r) in
((38358837682.21792636,38358837682.21792637)). At (x=r)
the gap is zero. The least integer onset is (38358837683).
D02 cannot move either onset earlier. The inherited finite
argument uses Dudek–Platt §3.1 and Lemma 3.4 (PDF pp.8, 10);
retain Dudek–Platt Theorem 1.2 (PDF p.2) and Platt–Trudgian Theorem
2 (PDF p.3) on its valid domains, not its literal real reading
on (38358837682<x<r).
The new secondary early analytic positivity proof already
starts at log (36.53), providing another overlap with the
original finite bridge. The local branch
(R(x)>67{,}000{,}000(x-r)) holds for (r<x<38358837683):
at fixed counts (R'(x)=e,632207037,(t-1)/t^2), decreasing
on that cell, and the endpoint derivative is certified.
There is also a finite B0 bound (G>.000007) on
([38358837683,38358847682]) in **(x)** coordinates.
See `localgap.py`: start with the reviewed near-root counts,
sieve both short integer ranges by every prime up to their
square roots, and enclose (lfloor m/e
floor) at each
integer (m). The result uses the lower gap at (m)
((ex/log x) and (pi(x/e)) increase on ([m,m+1)),
(pi(x)) is constant) and lower normalizing factor
((log m)^6/(m+1)^2). The final integer is tested separately.
This finite margin is not asserted across the unsieved part
of the Dudek–Platt bridge.

## Stronger small-onset bounds (B0)

At the following log onsets each constant (c) means
(G(t)>c) on the **whole** ray. Each new finite proof ends
at (43.16), where the inherited (G>1) ray applies.

| log onset | (c) | log onset | (c) |
|---:|---:|---:|---:|
| 36.55 | .01 | 39.542 | .25 |
| 36.60 | .035 | 39.67 | .30 |
| 36.70 | .08 | 39.90 | .385 |
| 36.76 | .10 | 39.998 | .415 |
| 36.962 | .20 | 40.23 | .50 |
| 37.006 | .219 | 41.36 | .80 |
| | | 42.50 | 1 |

At fixed .20, .25, .50, .80, 1 the corresponding prior certified
onsets were (36.99,39.61,40.5,41.93,43.16). These are sufficient
onsets, not claimed optima. Additional strict finite windows
are ([44.7,65]:1.18, [45.1,65]:1.22, [46,63]:1.25,[47.1,59]:1.28, [48.01,53]:1.30).
Old finite-window and later branches are not deleted.

Proof: optimize the CH2 Proposition 9.1 (J)-transfer in
`ramanujan.md` (PDF pp.34–36) over the larger finite height set
in `early.py`: (10^6{10,12,ldots,150,200,300,500,800,1000}),
all below (e^{21}) and the FiniteRH height. Keep the anchor
(e^{21}), the (J_{1/2}) error (<50) and the endpoint
error at the anchor unchanged. For (35le ule58), the upper
prime-power correction is now the decreasing expression
(mathrm{Jcor}(u)) from `verify.py`, not its rounded upper
constant 1.08. For the lower correction on this same domain,
use (1+2/u+8/u^2) instead of 1 by applying Dusart Corollary 5.2,
(5.4), PDF pp.15–16, at (e^{u/2}>88789) to the square term.
Both directions use normalization (u/e^u) and the correction
is a factor multiplying (e^{-u/2}). All new error terms still
decrease: for the positive direction,
(e^{-u/2}(C-1-2/u-8/u^2)) decreases, since (C>2),
(uge35) and differentiation gives a negative derivative;
for the other direction use monotonicity of (mathrm{Jcor}).
Extend the sign cut to (39.471), still strictly below
(log(1.39cdot10^{17})) (Dusart p.15).
Apply the inherited degree-52 minorant and exact cell check,
now with adaptive subdivision. Use a one-sided count cap
at (t) and independently at (t-1), cutting also at shifted
changes of branch. Overlapping endpoints are included.

## Matched B0 and D02 advanced profiles

Let (g_j=sum_{i=0}^{j+4}(i!inom{j+4}{i}-i!(j+4-i)!)) and
(M_j(t)=sum_{i=0}^j g_i/t^i); the first terms are
(1,14,145,1412,13985,145450,1610021).
Use (8)–(9) of `d02-proof.md`, including the exact
(mathcal L(t)=t^6(f(t-1)/t-f(t)^2)) pointwise bound.
There is no weakening at any (t): take the maximum of
all older valid lower bounds and all new ones of either
premise class available to the user. In (9), use the smaller
error separately in the two directions and at the shifted
and unshifted arguments; for small (t) retain the older
(operatorname{Li}) barriers and capped weight branch.

Matched non-polynomial comparison: the new D02 pointwise
branch in (9) is strictly greater than the bound using the
furnished QRH/B0 counting-error envelope, for **all** (tge171).
Indeed for every counting argument (sge170), anchor 165
in (8) gives a scaled counting cap (<.33 e^{-5s/32}),
the check at 170 applying to the whole ray after rescaling
by (e^{5s/32}). The rescaled anchor term decreases as
(s e^{-bs}) and the integral factor decreases as well.
The inherited symmetric caps in use there are each at
least (min(1.05cdot 10^{-12},.0161e^{-s/8})).
Every *new* (B_0) anchor cap is at least
(.005 e^{-s/8}): for all its anchors (age150), the
last band in (2) starts at .87 and supplies
(>.0105(1-e^{-.005a})>.005), by integrating the positive
term and lower-bounding its exponential growth away from
the right edge by 1. In (3) the cap is larger than .0106.
Now (.33e^{-5(170)/32}<1.05cdot10^{-12}) and
(.33e^{-170/32}<.005); both comparisons persist.
Since (s=t-1,t), the larger of the necessary onsets is
(t=171), not 170. This compares actual certified
error budgets in the two explicit envelopes (not the
unknown true error). Asymptotically this is a saving
of (x^{-1/32}), up to constants; both sides of the
Li approximation are also bounded, by the symmetric
version of (9). The exact-Li comparison does not
exclude further B0 arguments or claim independence.

For a compact absolute-discrepancy comparison, these (D)
give (|G(t)-mathcal L(t)|< D t^4 e^{-(1-b)t}) on the
whole ray starting at the listed log onset:

| log onset | B0 (b=7/8) | D02 (b=27/32) |
|---:|---:|---:|
| 180 | .0669 | .960 |
| 190 | .0634 | .910 |
| 200 | .0606 | .8782 |
| 220 | .0582 | .830 |
| 250 | .0545 | .776 |
| 300 | .0507 | .721 |
| 550 | .0425 | .604 |
| 600 | .0397 | .563 |

Here (8) rescaled is decreasing past the anchor, so bound
both counting arguments using the normalized bound at onset
minus 1, and replace (t/(t-1)) by its onset value in (9).
The certificate gives both tails simultaneously; for instance
at (tge200) the candidate-to-control cap ratio is
((.8782/.0606)e^{-t/32}<.028).
For an even smaller pointwise budget take (9) directly.
Equation (8) also allows any real anchor (age150)
with a valid bound at (a); the checks for the rounded
table only use the stated discrete anchors.

Whole-ray strict profiles with finite joins and analytic tails
(([c_0,ldots,c_j]) means (sum c_i/t^i)):

| log onset | profile | premises |
|---:|---|---|
| 47.68 | (M_1) | B0 |
| 49 | ([1,14,2]) | B0 |
| 49 | ([1,14,64]) | D02 |
| 49.4 | ([1,14,75]) | D02 |
| 49.5 | ([1,14,76]) | D02 |
| 168 | ([1,14,77]) | D02 |
| 180 | ([1,14,131]) | D02 |
| 186 | ([1,14,142]) | D02 |
| 188 | (M_2) | D02 |
| 222 | (M_2) | B0 |
| 200 | (M_2+1170/t^3) | D02 |
| 212.3 | (M_3) | D02 |
| 213 | (M_3+2000/t^4) | D02 |
| 238 | (M_4) | D02 |
| 240 | (M_2+1200/t^3) | B0 |
| 260 | (M_4+139000/t^5) | D02 |

For exact higher-order (M_j) onsets, additional certificates
with a common degree-100 polynomial give the following
sufficient log thresholds (take the minimum when another
branch proves the same target earlier):

| (j) | B0 | D02 | (j) | B0 | D02 |
|---:|---:|---:|---:|---:|---:|
| 5 | 324 | 264 | 12 | 575 | 451 |
| 6 | 360 | 291 | 15 | 685 | 533 |
| 7 | 396 | 317 | 18 | 794 | 615 |
| 8 | 431 | 344 | 19 | 830 | 642 |
| 9 | 467 | 371 | 20 | 867 | 670 |
| 10 | 503 | 398 | 24 | 1013 | 779 |
| 11 | 540 | 424 | 28 | 1160 | 889 |
| 32 | 1307 | 999 | 37 | 1490 | 1136 |
| 43 | 1712 | 1303 | | | |

For rows below 150, first certify from the given log onset
through 150 with the early code (unless joining earlier
to the inherited constant rays). Use the degree-100
certificate for any remaining finite piece, then the
monotonic tail bound of `d02-proof.md`. Each join and
choice of multiplying power (t^k) is in `claims.py`.
This is why the low-onset D02 rows, though starting earlier
than the input, can be stronger as *connected rays*:
their early finite proofs use B0, but their joins through
the intermediate finite-height bottleneck use the D02 strip.
Comparing at the fixed target (M_2) gives 222 versus 188;
at (M_{19}) it gives 830 versus 642, including the entire
tail beyond the latter. At fixed onset 49 the exhibited
third coefficient goes from 2 to 64; this is not an
assertion that 2 is optimal with original premises.
`sharpness.md` gives a converse for the exact Li-error
exponent itself.

## Linear onsets at arbitrary high order

For every integer (jge35), set (n=j+5). Then:
[
egin{array}{c|c|c}
	ext{premises}& t	ext{ onset}&	ext{strict lower profile}\ hline
B_0 &37n &M_j+.14 n!/t^{j+1}\
B_0+mathrm{D02}&28n &M_j+.07 n!/t^{j+1}\
B_0+mathrm{D02}&37n &M_j+.18 n!/t^{j+1}.
end{array}
]
In particular .07 is available at a reduced slope, and at
the same onset 37n the certified .14 increases to .18.
These are additional branches, not a replacement for any
better fixed-order ray. More generally, let (cge27) be any
rational with (arrho=ce^{1-alpha c}<1); require (nge40)
and (.57arrho^nle .116) for D02 (for B0 use .042 in
place of .57). Then a strict margin (.05n!/t^{j+1})
is valid on (tge cn). This provides a terminating
explicit check for the order threshold at every such
slope; no claim of an optimal slope.

Proof. On (vge27n), use the integrating-factor identity
for (f-S_n) starting at (v/2). Both functions are positive
at (v/2), (f(v/2)<1.04/(v/2)) by the inherited barrier,
and (S_n(v/2)le 1/((v/2)(1-2n/v))) by its term ratios.
Thus the remaining anchor contributes at most (3e^{-v/2}/v).
Relative to ((n+1)!/v^{n+2}), this is at most
(3(27e)^{n+1} e^{-13.5n}), by monotonicity of
(v^{n+1}e^{-v/2}) and
(m!ge(m/e)^m) (integrate (log u) from 1 to (m)).
It is (<1/8) using (27e<81, e^{13.5}>2^{13}),
and the integer check at 40. The integral from (v/2)
to (v) in the remainder is between
((1-e^{-1})/v^{n+2}) and (1.1/v^{n+2}), using ([v-1,v])
for the lower bound and differentiating (e^u/u^{n+2})
for the upper. Hence (S_n<f<S_n+2(n+1)!/v^{n+2}).
For (tge cn) with possibly (t-1<27n), use this barrier
at (t-1) whenever (c>27) and (t-1ge27n).
In the claimed generalization this follows from
(arrho<1): (arrho>1) at (c=27.1) in both premise
classes and (ce^{1-alpha c}) decreases for (cge27),
so (c>27.1). It holds a fortiori at 28 and 37.

Truncate the positive shifted lower series at degree (n+2)
before multiplying by (t^6). All gap coefficients through that
degree then agree with the true ones, including (g_{j+1});
the extra term in the upper (f) first contributes at degree
(n+3) in the square. Dividing by (n!/t^{n+2}) before
multiplying by (t^6), the next true coefficient is
(g_{j+1}/n!ge 2/3-4/n>.566) as in `orders.md`.
Bound the discarded square tail of (S_n^2) by
(3(2n/t)/(1-2n/t)), since at unscaled degree (q+2)
its coefficient is (le 3q!), and
(q!/n!le(2n)^{q-n}) for (n<qle2n).
The extra cross term costs (le 4(n+1)/(t(1-n/t)))
and the extra square (<.001), directly from
((n+1)!/t^{n+1}le ((n+1)/t)^{n+1}).
The total is (<.384) for (cge28), and (<.400)
for (cge27). The normalized counting budget before
multiplication by (t^6) is (<D e^{-alpha t}/t^2)
with (D=.57) (D02) or .042 (B0): use (8) from 550
rescaled at 600, giving (V<.178e^{-5t/32}) or
(.013e^{-t/8}), and include the shift as in (9), with
(t/(t-1)le601/600) for (tge601).
Dividing by (n!/t^{n+2}), this is at most
(D(ce^{1-alpha c})^n), again by monotonicity.
The numerical checks (arrho<.96) at (c=28) for D02,
(arrho<1) at (c=37) for B0, and
(arrho<1/3) at (c=37) for D02 give the stated margins.
The common arithmetic constants and derivative checks are
in `claims.py`. This argument does not require
asymptotic-series truncation at an order independent of
the requested (j); it proves each separate whole ray.
