# Repair and stronger Mertens envelopes (B0)

All notation, normalization, finite branches and strict/real endpoint conventions
in mertens.md remain in effect. This file improves the analytic and finite/analytic
join envelopes; use their pointwise minimum with every retained valid branch.
All improvements in this file hold **without** D01. By common.md the comparison with
the strongest lawful original-input envelope is exactly equality even for the
new signed intersections and movable onsets. The specific comparisons with
Dusart 5.6–5.9 are below and in mertens.md.

## Scope correction

The former wording “In each transform” is withdrawn **if interpreted to use the
unshifted ψ spectral bound for θ**. Write
(q(t)=e^{-t}(psi(e^t)-	heta(e^t))), so (u_	heta=u-q). At (L=17),
Dusart Prop. 4.3, PDF p.12, gives
(int_L^infty qge 1.9998e^{-L/2}>2J_1(L)), where (J_1) is the old
ψ-tail bound. Thus (int_L^infty u_	heta<-J_1(17)), using the valid
(int_L^infty ule J_1(17)). The strict comparison is in spectral_repair.py.
The θ identity and its signed local-and-integrated θ bounds are valid; only the
unshifted spectral assertion for θ is false. None of the earlier numerical
constants used that assertion.

The following replacement actually gives a spectral interval for θ, with its
center adjusted by the prime-power contribution. It also improves the ψ branch
even when the θ alternative is unused.

## 1. Sharper signed spectral integral

For (Lge1) and either (k=1) or (k=K), put
[
 Z(L)=.1e^{-L/2}+4cdot10^{-12}e^{-L/8},qquad
 J(L)=Z(L)+2e^{-L}.
]
Then the **ψ** integral belongs to
[
 int_L^infty u(t)k(t)dt in k(L)[-Z(L)-2e^{-L},,Z(L)].
 	ag{1}
]
The θ integral belongs to this interval **minus**
[
 left[int_L^infty q_-(t)k(t)dt, int_L^infty q_+(t)k(t)dt
ight],
 	ag{2}
]
where (q_+=1.000000147 e^{-t/2}+1.78 e^{-2t/3}) from Dusart Cor. 4.5
(PDF p.13), and (q_-) is zero for (t<log121) and
(max(.9999,1-4/t^3)e^{-t/2}) otherwise (Dusart Prop. 4.3).
The interval subtraction rule is ([a,b]-[d,e]=[a-e,b-d]). This is a
direct whole-ray proof even at values where an unshifted bound would fail.

**Zero weights.** From FKS Lemma 2.1 and Remark 2.2, PDF pp.4–5, the positive
ordinate count has main term (M_0(t)=tlog(t/(2pi e))/(2pi)+7/8), error
at most (r_0(t)=.137log t+.443loglog t+1.588).
For (yge100), partial summation over (gamma_
hoge y), with the
pre-jump count at y (same upper/lower continuous bounds via limits), gives
[
 sum_{gamma_
hoge y}gamma_
ho^{-2}
 le rac{log(y/(2pi))+1}{2pi y}
       +rac{2r_0(y)+(.137+.443/log y)/2}{y^2}.
 	ag{3}
]
Indeed the main term integrates (M_0'(t)/t^2), and
(r_0(t)le r_0(y)+(.137+.443/log y)log(t/y)) for (tge y).
Add the low ordinates using
(sum_{0<gamma_
ho<100}1/gamma_
ho<.5922435112)
(FKS Table 1, PDF p.5) and (gamma_
ho>14)
(CH2 Appendix B.1 immediately before Lemma B.1, PDF p.43,
extraction physical LF 6133–6143). Doubling for both signs, (3) gives
(sum_
ho gamma_
ho^{-2}<.1), and
(sum_{|gamma_
ho|ge H}gamma_
ho^{-2}<4cdot10^{-12}) for (H=3cdot10^{12}).
These comparisons are directed, not asymptotic. Below H use finite RH,
and above H use the original QRH conclusion, including possible equality
(eta=7/8).

**Kernel loss.** For a Laplace kernel (k(t)=int_{[0,infty)}e^{-vt},d
u(v))
with nonnegative measure and finite (k(L)), a term with exponent
(
ho-1) integrates on the full ray to
[
 int_{[0,infty)}
        rac{e^{(
ho-1-v)L}}{1-
ho+v},d
u(v).
]
Its magnitude is at most (k(L)e^{(eta-1)L}/|1-
ho|), since
(|1-
ho+v|ge |1-
ho|). On finite intervals a second endpoint costs at most
the same amount. Constant (k=1) is the unit atom at zero, and (K) is
the positive density (1+v). The compact (L^2) convergence proof for
Dusart's (2.1) in mertens.md justifies integration before the upper endpoint
tends to infinity. Even if the density table is withheld, absolute convergence of the actual ψ integral follows from the density-free estimate in common.md. The finite-interval estimate times (|
ho|^{-1}) and (3)
give a summable dominating sequence; pairing signs is valid by absolute
convergence after integration. The decaying elementary residual in (2.1)
is negative for (tge1), has magnitude at most (2e^{-t}),
and (k(t)le k(L)). This proves (1); subtraction of the integrable
(q) proves (2). No θ series is asserted.

## 2. Better signed prime-power tails

Put (c=1.048cdot10^{-12}) and (d=c+114e^{-14.5}). On (tge7),
[
 |u_	heta(t)|le 3e^{-t/2}+d .
]
On ([7,29]) this follows even with (d=0) by CH2 Lemma 9.2 (PDF p.35)
and the upper prime-power cost (q_+).
Above 29, CH2 Cor. 1.3 (PDF p.3) and (q_+) give (c+117e^{-t/2}).
For all (zge e^{14/3}) one also has (	heta(z)le1.08z), using
(	hetalepsi) and the positive CH2 bounds on the same two branches
(now starting the first branch at (14/3)). The endpoint checks of all
constants are in spectral_repair.py.

For (Lge14) and (y=e^{L/2}), partial summation gives for the square part
(V_2=sum_{p>y}log p/p^2):
[
 |V_2-e^{-L/2}|le (7e^{-L/4}+3d)e^{-L/2}.
]
In fact the error is at most (y^{-1}(3y^{-1/2}+d)) at the lower boundary plus
(2int_y^infty(3z^{-1/2}+d)z^{-2}dz).
For the higher powers put (w=e^{L/3}). If (p>w), majorize the geometric
sum by (p^{-3}/(1-e^{-L/3})), and the partial summation bound is
(sum_{p>w}log p/p^3le(3/2)1.08w^{-2}) by dropping the negative boundary.
If (ple w), the first allowed power exceeds (x) and the tail is bounded
by (2	heta(w)/xle2.16e^{-2L/3}). Therefore
[
 Vinleft[max(0,1-7e^{-L/4}-3d)e^{-L/2},
     widehat V(L)
ight],qquad
 widehat V=(1+7e^{-L/4}+3d)e^{-L/2}+3.8e^{-2L/3}.
 	ag{4}
]
All statements include (p^m=x) on the *non-tail* side.

A further optional lower branch for (U+T_0) is
[
 max(0,1-2/L-3eta_y),e^{-L/2}/L,qquad
 eta_y=3e^{-L/4}+d.
 	ag{5}
]
Use its square subtail ((1/2)int_{(y,infty)} f(z)d	heta(z)) with
(f(z)=1/(z^2log z)). The main integral (int_y^infty f(z)dz) is
at most (1/(ylog y)) and at least ((1-1/log y)/(ylog y)),
by substituting (z=ye^v) and bounding (1/(1+v/log y)) between
(1-v/log y) and 1. Partial summation with
(|	heta(z)-z|leeta_y z) costs at most
(eta_y[2yf(y)+int_y^infty f]), before the factor (1/2).
For U alone subtract the (T_0) upper bound from (5), and clip at zero.
For both upper bounds use (widehat V/L) or the old (V_b/L), whichever
is smaller. These corrections can be intersected with all old corrections
using the same exact identities.

## 3. Whole-domain pointwise envelope and uniform tradeoffs

In the ψ transform for each error and in the A bridge in mertens.md, additionally
intersect with (1); in the separate θ sum transform additionally intersect with
(1)–(2), retaining the signed θ endpoint integral as a competing bound.
Insert (4)–(5) into the appropriate ψ formulas and use the original no-correction
θ formulas (do not add a prime-power tail twice). At (10^4le xle 10^{13})
one may also use the signed ψ interval ([-.751,.791]e^{-L/2})
from the sharper limited-range minimum in CH2 Lemma 9.2. On ([34,58])
one may add the local ψ interval from CH2 (9.4), verified in the same
parameter range as in ramanujan.md. All choices are pointwise on their own
domains. Then perform the separate signed-to-relative conversions of
mertens.md, intersecting valid branches and retaining the original Dusart
and finite-sieve bounds in the minimum. At (1<x<2) use the exact empty sum
and product. This prescription never relies on a computed switching point.

Here is an explicit common unsigned branch, convenient for proving uniform
comparisons. For weighted error use (W_*), and for the other three scaled
log/sum errors use (W_*/L) before exponentiating for the two products:
[
 W_*=
 egin{cases}
  2.61 e^{-L/2} &14le Lle17,\
  2.25 e^{-L/2} &17le Lle29,\
  (L^2/(8pi)+1.25)e^{-L/2} &29le Lle58,\
  c+115e^{-L/2}+4.1cdot10^{-12}e^{-L/8} &58le Lle 189.24,\
  D(L)+(1+1/L)J(L)+widehat V(L) &Lge189.24 .
 end{cases}
]
At a shared endpoint both bounds are valid. To see this, use the unsigned
consequence of (1), and for (u) use the CH2 first band, finite RH second,
CH2 Cor. 1.3 third and density last band as in mertens.md. In the first
three bands, scale by (e^{L/2}): only the high-zero exponential term grows
(thus use the right endpoint there), while the other reserve terms decrease.
On the fourth band compare constant factors separately at 58.
On the last band (e^{L/8}W_*) and (W_*/L) decrease termwise.
Exponentiating gives the bound (W_* e^{W_*/L}/L) for both products,
with (e^{W_*/L}<1.0002) on the first band and (<1.0001) thereafter.
For the middle powers use the decaying scaled terms at the left and the
CH2 floor at the right. For the scaled polynomial comparisons use the
left endpoint for each decreasing term, the right endpoint for the CH2
floor times (L^2), and (L^2e^{-L/8}) decreasing for (Lge16) on
the last band. These inequalities prove all analytic joins via endpoint
comparisons in spectral_repair.py, not evaluations of primes on a grid.

For the polynomial scale (powers (L^3,L^3,L^3,L^2)), all four errors are
strictly below .133 for (Lge17), .120 for (Lge17.3), and .091 for
(Lge18). This is strictly stronger than the old .2 and .3 on the
whole matched rays. In addition .120 for the first three and .12722
for the weighted error each holds from **(x=10^7)** on the whole
closed ray: use the old integer-interval certificates smallprod.log and
weighted.log through 66 million, and join from (L=17.3) and (L=17.16),
respectively. These replace the older common .130 from the same onset
without discarding the earlier finite or exact-point branches.

For the power scale (multiply the first three errors by (L e^{L/8}),
the weighted error by (e^{L/8})), the shared strict bound for (Lge14)
is **.019675**. Later uniform constants improve further:

| log-onset | 200 | 300 | 500 | 1000 | 3000 | 30000 | 1000000 |
|---|---:|---:|---:|---:|---:|---:|---:|
| coefficient | .018857 | .015169 | .013103 | .011821 | .010979 | .010514 | .010453 |

The limiting loss of this power-scale approach is the far-right reciprocal
zero weight in (D); reducing the integrated spectral term does not remove
that local weight. The uniform early power coefficient is governed by the
join of the CH2 floor with the density bound, not by the early finite interval.
The .019675 branch remains incomparable with the old polynomial branches on
their full matched domains: the ratio test is the same (K L^2e^{-L/8})
as in mertens.md, with the brackets checked below. This does not prevent
the full pointwise minimum from dominating both.


The unique crossing of the new uniform power profile with Dusart's .2 on
the first three matched domains is in ((40,41)) in log scale, and with
.3 for the weighted matched domain it is in ((35,36)).
The ratio (L^2e^{-L/8}) increases to 16 and strictly decreases thereafter;
it is already above the target after multiplication by .019675 at the
respective original onsets. spectral_repair.py checks both brackets and the
earliest comparisons with directed arithmetic. Keep the polynomial branches
where they win; there is no assertion that the early extension of the power
branch beats them everywhere.

## 4. Earlier verified power onsets

The finite program power_bridge.py extends the latest uniform power branch
to the following real, closed rays. The first coefficient applies to **both
products and the reciprocal sum**; only the weighted error uses the second.

| real onset | first three | weighted |
|---:|---:|---:|
| 50000 | .0268 | .0292 |
| 60000 | .0248 | .0272 |
| 70000 | **.019675** | .0214 |
| 104000 | .019675 | **.019675** |

Every entry is strict in the power scale stated above. The same-coefficient
onsets 70000 and 104000 are earlier than 100000 and 500000 for the old,
larger .01970 bound.

**Finite proof.** All primes through the composite endpoint (T=1202606>
e^{14}), and also through the larger normalizer cutoff (N=5000000), are
enumerated by early.primes. Use the proof of the gamma interval in mertens.md
with (n=10^5). For (M) subtract the positive log-series prefix and
bound the remaining tail by (1/(2N)). For (B_3) add the weighted prefix
and use the same signed theta tail error ((.2/log^2 N)
[2/(N-1)-log(1-1/N)]) around the main
(-log(1-1/N)) as in the old extended weighted bridge. Dusart Thm 4.2
applies at this (N). The older verified log and loglog blocks,
rational series, and outward fixed scale (S=10^{20}) are reused with these
cutoffs. For each prefix through prime (p_0), test the full cell
([p_0,p_1)) clipped by the query onset, conservatively taking the
pre-jump limit at (p_1); then test the next cell with the updated prefix.
The final cell through (T) is closed. Because the three log/sum errors
there are of the form constant minus either (log x) or
(loglog x), evaluate their outward extrema at the clipped left
endpoint and the right endpoint. If the enclosed (|D_Q|) has
upper bound (b<1/10), then the **two** product errors are bounded by
(b/(1-b)), since (e^b-1le b/(1-b)). To handle the power scaling
on the *whole* cell, multiply the unscaled maxima by the log upper bound
at the cell's right endpoint where appropriate, and by
(exp((log r)/8)) outward, where (r) is the first member of an
increasing integer list of endpoints at or above that right endpoint.
The list uses steps (lfloor r/200
floor), capped at (T); its role
is only to reuse upper scale factors. No assumption that a cell stays
within a slab is needed. All products and sums after scaling the log
bounds use exact integers, and the end-of-run assertions check the
stated coefficients. The early upper certificates for the .019675
tolerance do not pass at 60000 (first three) or 100000 (weighted).
They are not lower witnesses or a proof of optimal onsets.

## 5. Robustness of the polynomial branches

The newly tightened polynomial envelopes (.133, .120, .091, including the
finite joins) do not require the FKS density-table premise. To avoid it,
extend the CH2-floor band from 58 to 230. At (Lge230) replace (D) in
the last row by
(.0142L^2 e^{-L/8}+2.091 L e^{-L/4}), the density-free truncation in
common.md. All expanded terms of (L^2W_*) are nonincreasing on this
last ray: the largest power against (e^{-L/8}) is 4.
The directed checks at 230 prove (1.0001L^2W_*<.091) there and
verify the exponentiation factor for the whole extended middle and
late branch (the middle exponential loss was already bounded at 58
by its decreasing unscaled terms). Thus the same early polynomial
strict-ray joins, including the previously retained fractional
Dusart comparisons, have a tail even if Cor. 2.9 is withheld. The
fixed-coefficient (x^{-1/8}) profiles still use the stated density
corollary; this alternative would cost logarithms there.
