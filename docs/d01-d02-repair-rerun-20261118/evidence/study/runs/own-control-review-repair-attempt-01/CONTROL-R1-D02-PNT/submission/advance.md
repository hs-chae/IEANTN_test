# Additional research during the repair

The labels B0, B1, \(e,K,H,h,b_j,a_j\) are unchanged (B1
adds exactly PsiMajorant). This supplement is additive: take maxima of
valid lower profiles and minima/intersections of applicable upper
enclosures. All log-onsets below are inclusive and real. The
original FKS density corollary's separate trust tier remains as
stated in spectral.md; the new height-choice results do not use it.

## 1. Better density-free bounds (both families)

Use FKS Thm. 3.2 (PDF p.8, text 631–642) with
\(T=L e^{a_jL}\) instead of \(e^{L/3}\).
On \(L\ge40\), \(T>\max(51,L)\), \(5T+2<e^{L/2}\):
check at 40 and then use \(a_j+1/L<1/2\) for monotonicity of
the ratios. For \(Y=a_jL+\log L\) this gives
\[
 d_{\rm light,j}(L)=
 (3.491+.17(Y+1)(Y+2))\,e^{-a_jL}\ge |e(L)| .
\]
The truncation contributes \(2.091e^{-a_jL}\); the reciprocal zero
sum through \(T^\star\le2.45T\) is \(\le1.4+.17(Y+1)(Y+2)\)
by the same FKS Lemma 2.1/Cor. 2.3 arithmetic used for S1
(PDF pp.4–5, text 275–347). The log bounds use
\(\log2.45<1\) and \(\log(10/(2\pi))<.5\). Thus the limiting
coefficient in units \(L^2e^{-a_jL}\) is at most \(.17a_j^2\)
instead of \(1/16\) from S1.

A stronger option on many compact domains uses the full finite-RH height.
Set \(v=Y+\log2.45\), \(W_+=\max(0,v-h)\),
\(R(h)=.137h+.443\log h+1.588\) (Rosser radius in log units), and
\[
 c_H^*=\frac1{2\pi}+\frac{.137h+.443}{Hh(h-\log(2\pi))}.
\]
Use the sharper majorant
\[
 d_{\rm split,j}=
 e^{-a_jL}\{2.091+2[c_H^* W_+((v+h)/2-\log(2\pi))+2R(h)/H]\}
 +[1.4+.17(h+1)(h+2)]e^{-L/2}.
\]
Indeed all low zeros through \(H\) are on the half line; the
bound for their reciprocals follows by limiting FKS Cor. 2.3
from \(V>H\). Above \(H\), if \(V=2.45T>H\), bound the
reciprocals by \(2 B_1(H,V)\) from FKS (2.1), taking \(V\)
from above for closed boundaries. If \(V\le H\) this sum
vanishes and we may use the nonnegative formula shown. Both
new bounds are valid on the whole ray \(L\ge40\), separately
for each \(j\). B1 can always retain any stronger B0 branch,
so the envelope is nested even if particular height choices
are not optimized or nested.

**Products and sums.** For all \(L\ge300\), the three errors
for the products and \(1/p\) are at most \(C L x^{-a_j}\);
the weighted sum error is at most \(C L^2x^{-a_j}\), with
\(C=.003814\) for B0, \(C=.005563\) for B1. These improve
the old density-free .0626 in each treatment on its full ray.
Use M4 with \(d_{\rm light,j}\) and the S8 \(k,J_k\) bounds.
The functions \(e^{a_j L}L^{-2}U\) and
\(e^{a_j L}L^{-2}(LV)/(1-V)\) decrease: \((Y+c)/L=
a_j+(\log L+c)/L\) decreases for \(c=1,2\); the other
nonnegative terms decrease after the same scaling. Also \(V\)
itself decreases (each \(Y+c\) has log derivative at most \(1/L\)
and \(2/L<a_j\)), so its left endpoint certificate proves
\(V<1\) everywhere needed. The constants are checked at 300;
the ratio of the new input case to the matched B0 case is
\((.005563/.003814)e^{-L/32}<1\) throughout. In both treatments
the corresponding \(\limsup\) in density-free scaling units
\(e^{a_j L}/L\) for the first three channels and
\(e^{a_j L}/L^2\) for the last is \(\le .17a_j^2\).
The endpoint choice allows arbitrary admissible heights if
one wants further pointwise minimization: no shared
Perron \(T^\star\) is needed across different \(x\).

**Sharper density-free Mertens coefficients, same onset.**
Using \(d_{\rm split,j}\) in M4 gives \(C=.00262\) and \(.00408\)
respectively, still from \(L=300\). In scaled units the split
factor equals the sum of decreasing positive terms minus
\(c_H^*(h-\log(2\pi))^2/L^2\). In fact \(v>h\) in these ranges,
and its square contribution is
\[
 c_H^*\left(a_j+\frac{\log L+\log2.45-\log(2\pi)}{L}\right)^2
 \ -\ c_H^*\frac{(h-\log(2\pi))^2}{L^2}.
\]
The first term decreases, as do the other positive terms
of \(e^{a_jL}LV/L^2\). The unscaled \(V\) also decreases:
the maximum log derivative of the split high polynomial-log
factor is less than \(a_j\) at 300 and then decreases, by
the derivative inequality below. This verifies all signs
needed for the relative denominator at left endpoints.
On each of the 440 real cells of width 5 from 300 to 2500
use the positive part and \(1/(1-V)\) at the left and bound
the subtracted term at the right. From 2500 simply omit the
negative term, retaining a decreasing analytic bound. All
cells and the analytic left anchor are tested in advance.py.
The treatment ratio has the same decreasing \(e^{-L/32}\)
factor. The limiting coefficient improves to \(c_H^*a_j^2\)
in the same units, since logarithmic factors divided by
\(L\) vanish and the other terms are \(o(1)\).
Keep the light branch too if an entirely monotone scalar
proof with only a single arithmetic check is desired.

**Ramanujan.** Here and below \(k,m\) are precisely the
R1 prefixes. The new checked density-free pairs are:

| \(k,m\) | B0 log-onset | B1 log-onset |
|---|---:|---:|
| \(2,145\) | 316 | 239 |
| \(3,1412\) | 353 | 268 |

These improve the original fallback pairs (360,275) and
(405,326) at fixed margins. Use \(d=d_{\rm split}\) in
R4 and in the \(b_D\) margin of R3, increasing \(1.63\) to
\(2.23\) in \(1+1.63/L\). To justify this last substitution,
on \(40\le u\le L\) the coefficient of \(e^{-a_j u}\) is
nondecreasing; the coefficient of \(e^{-u/2}\) is constant.
In the integral there, \(u^{-2}\le L^{-2}e^{2(L-u)/40}\),
so \(1/(1-1/2-2/40)<2.23\) suffices for both. Retain
the same early \(4\cdot10^7\) integral budget and both
prime-power drift terms. R4's \(J_j\) uses S8 as before.

On each cell for a row, \(d_{\rm split}\) decreases throughout
the applicable unshifted and shifted ranges. For its high
positive polynomial-log factor the log derivative of the
nonconstant product is at most
\[
 (a_j+1/L)\left(\frac1{v-h}+
                  \frac1{v+h-2\log(2\pi)}\right),
\]
decreasing once \(v>h\). The code verifies positivity of both
denominators and that the bound is less than \(a_j\) at 315
or 238 respectively, the earliest possible \(L-1\).
For the tail \(L\ge450\) its sum with \(14/449\) is less
than \(a_j\) already at 449 (covers all log powers allocated
to this term in the scaled loss); the low term, early budget,
drift, factorial remainder and negative main terms decrease as
in the original tail proof. Thus replacing branch errors by left
endpoints, except the subtracted drift using the right endpoint,
is valid before 450 and the single scaled-tail test at 450
is valid thereafter. See the executable cell subdivision in
advance.py, which reuses the existing R5 loss scheme.

## 2. Finer positive density mixture and certified tradeoffs

Use S3/S4 with width \(1/12800\) instead of \(1/3200\),
the same row data and running minima, including the artificial
terminal zero at the same cutoff. Denote its endpoint majorant
\(d_{\rm fine,j}\). Positivity and the upper-tail derivation
are unchanged; at common grid points the rounded S3 formula
uses the identical argument (and the same row), or one may
cap the refined running minimum by the original one there.
Within each original cell the refined running majorant does
not exceed the old left-bin constant (and the last endpoint
term remains part of the bound). This is a more effective
computable branch; S5 can still be included without claiming
that a finer step is stronger than the continuous integral.
The new replay uses a positive-coefficient Horner sum with
\(w=e^{-L/12800}\) and the denominator-free recurrence.

With the same normalization and convention as M1,
the following \(C\) replace the respective larger M1
coefficients in the indicated rows:

| log-onset | B0 \(C\) | B1 \(C\) |
|---:|---:|---:|
| 170 | .020787 | .292652 |
| 200 | .018115 | .254039 |
| 250 | .015824 | .221409 |
| 300 | .014599 | .204091 |
| 1000 | .011489 | .160892 |

Use \(d_{\rm fine}\) with M4. The same scaled positive-mixture
monotonicity at and beyond 170 applies (exponents at least
\(a_j\)); signed products are converted with positive
denominators. Each B1 row is smaller than its refined B0 row
on the whole respective ray by the exact ratio test.

The refined R1 profiles give:

| \(k,m\) | B0 log-onset | B1 log-onset |
|---|---:|---:|
| \(2,80.9\) | 196.58 | 48.95 |
| \(3,1412\) | 253.55 | 211.04 |

These have the same R2–R5 proof and tail as before, since the
positive exponential mixture has the same exponent ranges.
All branch breakpoints at both arguments are included.
For example at fixed onset 50, the B1 certified \(k=2\)
coefficient is now 80.9. At fixed \(m=80.7\), even the
stronger row starts earlier than the previously displayed
49/197 onsets. The attempted \(m=81\) from 49 remains
unsupported by this sufficient profile: the replay's optional
'explore' point at 168.72 shows the local dip (~80.9945).
This is not a claim of an arithmetic counterexample. The
active near-plateau term there is the old finite-height
branch before the new high-cutoff branch overtakes it.

### Full coefficients through order 12

For each row below take the full coefficient \(m=c_k\) in R1.
These are separate high-order real-ray certificates using the same
pointwise profile:

| \(k\) | \(c_k\) | B0 log-onset | B1 log-onset |
|---:|---:|---:|---:|
| 6 | 1610021 | 358.1 | 288.8 |
| 7 | 19063832 | 394 | 315.2 |
| 8 | 241691425 | 430 | 342 |
| 9 | 3277187246 | 466 | 369 |
| 10 | 47424796805 | 502 | 396 |
| 11 | 730550160076 | 538 | 424 |
| 12 | 11946592513217 | 575 | 450 |

The test at the left of the analytic tail (450 for \(k\le8\), 650
otherwise) works at the next scaled order \(d=k+1\), using
\(c_{k+1}>0\). The polynomial remainder \(L^{-21}\) still decays
after multiplying by \(L^{d+4}\), the shifted endpoint similarly.
The allocated exponential powers are controlled by
\(d+6<(L-1)/8\) on each corresponding tail. Certificates for the
finite joins are in advance_replay.txt. These rows give stronger
profiles later, not a reason to remove earlier rows.

## 3. Strict envelope comparisons, now from \(L=168.745\)

The radius floor \(f_0=\min(1.046\cdot10^{-12},.0104e^{-L/8})\)
of mertens.md §5 still works on this slightly enlarged domain.
The source constants and monotonic ratios justify the same
comparisons (on the plateau use through 190 as before);
for the refined B0 mesh its terminal coefficient exceeds
.0104 by the directed check. The two new density-free bounds
each include \(2.091e^{-L/8}\), so do not invalidate the floor.
The S5 and old signed \(K\) alternatives have the same
budget and centers. The new kernel option in §4 below adds
an interval containing 0 for its integral on this ray
(even if the elementary terms are separated as a signed
center: one may bound them by the stated symmetric radius,
and the half-line budget exceeds their magnitude; the
explicit preexisting signed-center variants use only S7/S8).
As before, loss of radius by signed prime powers is at most
\(3e^{-L/2}\) in scaled units. The new checks verify
\(LV/(1-V)< F_*(L)\) for \(L=168.745\), with
\(F_*=\min(1.045\cdot10^{-12},.01e^{-L/8})\) and
\(d=d_{\rm fine,1}\), and both ratios decrease on the ray.
The signed upper \(\pi\)-error before drift subtraction is
also less than both defining quantities of \(F_*\) at the
left endpoint, with the same declining ratios thereafter.
Thus the strict Mertens improvement holds on this enlarged
ray, and so does the strict R4–R5 improvement. No strict
gain on every point before this ray is asserted; B1 retains
all old bounds regardless.

For the original direct \(\pi\) branches in ramanujan.md,
one can now certify strict improvement of the *combined*
pointwise Ramanujan portfolio on this ray. Use the exact
smooth center \(\Xi_F=Le^{-L}F(e^L)\) in R3–R5, rather than
its finite polynomial lower and upper approximations: the
approximations were only for certification of table rows.
The old constructed upper endpoints before adding \(\Xi_F\)
are at least \(f_0-.9999e^{-L/2}>F_*\); the new construction
is strictly inside that. Each retained direct original-source
upper endpoint also exceeds \(\Xi_F+f_0\):
* For Dusart 5.1, R2 implies \(\Xi_F<P_2+6.3/L^3\).
  Check at 168.745 and use termwise decrease after scaling by
  \(L^3\). Thus the 7.32 (or 7.59) upper coefficient leaves
  more than \(1/L^3>f_0\): check through the plateau to 190,
  then use the increasing ratio to \(e^{-L/8}\). Here
  \(P_2=1+1/L+2/L^2\). For Cor. 5.2–5.3 the uppers are
  at least \(P_2+7.32/L^3\) by direct algebra. In particular,
  for the second rational upper expand the difference from
  \(P_2\) via \(y=1/L,\ c=1.2311\): its numerator is
  \((c-1)y^2+(c+2)y^3+2cy^4\), with positive denominator
  \(1-y-cy^2<1\); the first rational upper is at least
  \(1+1.112/L\). The remaining polynomial comparisons check
  at the left endpoint with decreasing inverse powers.
* For PT Cor. 2, the normalized radius
  \(235 L^{1.52}e^{-.8\sqrt L}\) exceeds twice both the
  center translation \((2/\log2)Le^{-L}\) and \(f_0\)
  from its own onset 2000. These ratios increase by direct
  logarithmic differentiation (replace \(f_0\) by its
  power part).
* The PT (19) published-anchor upper has distance
  \(>.002/L^5\) above \(\Xi_F\) on \(L\ge3914\) by repair.md
  and \(720B>.192\); again the ratio to the power branch of
  \(f_0\) increases (and is checked at 3914).

The stronger unshifted upper bound is strictly positive
(it bounds a nonzero prime count), so its square strictly
decreases. For the shifted lower, use B1's nonstrict
improvement from retaining all B0 options. This proves strict
improvement of the combined constructed/direct-source
lower profile, not an optimality assertion about all proofs
from B0. At these logs the sign-only finite theorem supplies
no stronger margin than the positive constructed profile.
All quantitative rows only certify subprofiles from their
underlying inequalities (or their maxima), so retaining those
rows cannot spoil this comparison.

### Strict improvement without the FKS density corollary

The same comparisons against the retained B0 envelope hold for
both families already throughout \(L\ge342\), without a density
estimate on the **B1** side: use \(d_{\rm split,1}\) in M4 and
in the signed R4 upper, and retain B0 options for the shifted
lower. The directed comparisons at 342 are to both terms in
\(F_*\). The high \(d_{\rm split}\) factor now has log derivative
less than \(1/32=a_1-1/8\) from 342 onward, by the same
decreasing product derivative inequality, checked at 342;
the other terms decay after both necessary rescalings. These
tests also prove the comparison entirely without FKS Cor. 2.9
if its branches are removed on the B0 side, since the floor
proof with those branches removed uses no density. Density,
when admitted on both sides, gives the stronger 168.745 result.

## 4. A sharper integrated Mertens transfer, and earlier signs (B0)

The extra derivative factor in the partial-summation estimate
of M4 is avoidable. For \(L\ge\log2\) write \(K\) from S7 as
an absolutely convergent exponential expansion with terms
\(c_z e^{-zu}\), \(\Re z>0\) (for zeros \(z=1-\rho\)).
For real \(t\ge0\), integrate by parts using \(-K'=e\):
\[
 \int_L^\infty e(u)e^{-tu}\,du
   = \sum_z c_z e^{-(z+t)L}\frac{z}{z+t}.
\]
Here we integrate \(K\), not its termwise derivative.
Absolute convergence at \(L\) permits the interchange for
\(t>0\); at \(t=0\) the formula is \(K(L)\).
The multiplier satisfies \(|z/(z+t)|\le1\).
For \(W(u)=1/u+1/u^2=\int_0^\infty(1+t)e^{-tu}dt\)
another absolute interchange is valid by integrability of the
scalar majorants (also directly using S1 for the initial
left-hand integral). Hence
\[
 \left|\int_L^\infty e(u)W(u)\,du\right|\le W(L) k_j(L).
\]
This holds also for any of the tighter **absolute sum**
budgets for S7. In M4 one can therefore delete the
\((1/L+2/L^2)J_k\) term in the numerator of \(V\).
The exact Mertens interval recipe can retain this new
integral enclosure whenever it supplies a smaller interval;
the \(A\)/weighted channel is unchanged. This is a strict
algebraic improvement of the scalar M4 log radius
throughout its applicable ray, not a promise that it
strictly beats all other branches everywhere. The checks in
§§1–3 conservatively used the older M4, so remain valid.

Here is a quantified early application independent of the
new input, using the same normalizations as mertens.md.
All four compact rays below end at \(L=\log(10^{13})\):
\[
\begin{array}{ll}
 E_\ell>.0012\,e^{-L/2}&(L\ge15.4),\\
 E_\ell>.0556\,e^{-L/2}&(L\ge18),\\
 E_1,\ Z_{\rm raw}>.00015\, e^{-L/2}/L&(L\ge20.6),\\
 E_1,\ Z_{\rm raw}>.0889\, e^{-L/2}/L&(L\ge20.77).
\end{array}
\]
Consequently the one-sided stronger \(P\) conversion
\(1-e^{-u}\) from a log upper endpoint \(u\) applies already
at 20.6. Use the lower CH2 Lemma 9.2 term and the same
absolute budget \(k_0\le .048 e^{-L/2}\) as before, now
valid from 15.4: after rescaling, put the increasing high
term at 30 and the decaying elementary terms at 15.4.
All arguments for CH2 are at least \(10^4\).
Include a cubic correction in addition to the square.
For \(y=e^{L/m}\), let \(\delta_m\) uniformly bound the
relative \(\theta\) error for arguments \(t\ge y\).
The tail rule of mertens.md gives for the weighted channel
a main \(y^{1-m}/(m-1)\) and relative error budget
\((2m-1)\delta_m\). For the unweighted channel with factor
\(1/m\), its main in units \(y^{1-m}/((m-1)L)\) is
\[
 \int_0^\infty\frac{e^{-s}}{1+ms/((m-1)L)}\,ds
\]
and its error in those units is at most
\((2m-1+m/L)\delta_m\) by differentiating the weight
and using \(\log t\ge L/m\).
For the square main use the integrated odd geometric
polynomial through degree 3 (gives
\(1-2/L+8/L^2-48/L^3\)); for the cubic use degree 1.
Use \(\delta_m=3.965m^2/L^2\) from Dusart 4.2, except
the sharper \(\delta_2=80/L^3\) from 20.77 onward since
\(e^{20.77/2}>32321\). All remaining corrections are
positive; for the product subtract at most \(1/x\) for the
tail \(p>x\) as before. In the resulting lower bound in
\(e^{-L/2}\) units (weighted) or \(e^{-L/2}/L\) units
(unweighted), the cubic contains \(e^{-L/6}\) times a
positive increasing factor; put the exponential at 30
and the other factor at the indicated left endpoint.
All remaining negative contributions shrink, and the square
main increases (its derivative is positive for \(L>16\)).
The directed inequalities in advance.py prove the displayed
margins and bridge the two alternative square-error domains.
