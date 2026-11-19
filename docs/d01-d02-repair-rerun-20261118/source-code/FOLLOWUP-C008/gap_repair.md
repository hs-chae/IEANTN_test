# Stronger Ramanujan margins and earlier factorial profiles (B0)

Definitions (R,Y,L), original-source comparisons, and the exact real last
failure (z) are as in ramanujan.md. They remain valid, including
(R(z)=0), (R(x)>0) for real (x>z), the least strict integer onset
38358837683, and the local derivative margin. This supplement is a new
**input-independent** improvement; it holds already under B0. The proof
of redundancy in common.md compares B0+D01 to the **full** B0 envelope,
not only to these particular branches.

## Certified strict normalized lower bounds

For every real L in each indicated closed interval the inequality is
(R(e^L)>q,e^{2L}/L^6), or (Y(L)>q).

| Closed log range | q |
|:--|--:|
| [36.54,∞) | .002 |
| [36.745,∞) | .1 |
| [36.91,∞) | .164 |
| [36.98,37.5] | .2 |
| [37.5,39.326] | .4 |
| [39.1,39.326] | .84 |
| [39.3,39.326] | .88 |
| [39.94,∞) | .4 |
| [40,∞) | .425 |
| [42.482,∞) | 1 |
| [43,60] | 1.06 |
| [45,77] | 1.209 |
| [46,67] | 1.246 |
| [47,61] | 1.27 |
| [48,55] | 1.30 |
| [49,52] | 1.32 |
| [59,80] | 1.20 |
| [80,100] | 1.15 |

For the rays use the finite cells listed in gap_repair.log and the original
valid [60,163] unit-margin check in verify.log; that check overlaps the
new (P_4=1) tail from 161. In particular the .164 join includes both
sides of (L=39.326); the sign-of-(pi-operatorname{li}) input is used
only up to this join, not beyond it. The real onsets are (x=e^a), exactly,
not integer rounding. For the old whole-ray margins .065, .145, .35, 1,
sufficient log-onsets improve from 36.98, 39.5, 40, 42.8 to
36.745, 36.91, 39.94, 42.482 respectively. At fixed onsets 36.98 and
39.5 the guaranteed margin is now .164, and at 40 it is .425.
The strict sign onset (x>z) stays unchanged, and no fixed eventual margin
(q>1) is possible by the two-sided limit in ramanujan.md. Take the
pointwise maximum of all valid lower profiles, including the old ones.

For (P_n=sum_{j=4}^n C_j L^{4-j}), where (C_j) are the full factorial
coefficients (equivalently computed with any truncation degree (ge j)),
the improved **closed** onsets for (Y>P_n) are:

| (n)| 4 | 5 | 6 | 8 | 10 | 12 | 14 | 16 | 17 | 20 | 24 | 32 | 48 | 64 |
|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| (Lge a)| 160.54 | 189.18 | 220.73 | 288.15 | 358.34 | 429.78 | 501.87 | 574.34 | 610.67 | 719.91 | 865.96 | 1158.82 | 1745.95 | 2333.94 |

These supplement rather than revoke the arbitrary-order method of
ramanujan.md. They are sufficient onsets, not optimality assertions.

## Proof of the improved finite profiles

Take (B(t)=int_t^infty u(s),ds), where
(u(t)=e^{-t}psi(e^t)-1). By (1) of spectral_repair.md,
(|B(t)|le J(t)) for (tge1). This uses the original QRH and finite-RH
conclusions but not FKS Cor. 2.9. For (w(t)=e^t/t^2), (tge7),
integration by parts of the absolutely continuous (B) gives
[
 int_7^L w(t)u(t),dt=w(7)B(7)-w(L)B(L)+int_7^L w'(t)B(t),dt .
]
Since (0<w'le w), integrate the two exponential parts of J
using logarithmic derivatives (ge1/2-2/7=3/14) and
(ge7/8-2/7=33/56), respectively. The residual (2e^{-t})
in the integral with (w') costs at most (2/7).
The (non-spectral) initial prefix from (log2) to 7 plus (2/log2)
costs at most (3e^7) by the old elementary theta bound (non-strict)
in ramanujan.md. Combining these and (w(7)J(7)+2/7<1),
the prefix and the integral from 7 to L with ψ in the integrand,
after normalization by (Le^{-L}), are bounded in absolute value by
[
 W_pi(L)=(3e^7+1)Le^{-L}+
 rac{.1(1+14/3)e^{-L/2}+4cdot10^{-12}(1+56/33)e^{-L/8}+2e^{-L}}L .
]
In the same integral and local term from the partial summation formula,
the prime-power discrepancy has nonnegative magnitude. Its combined
upper and lower bounds are
[
egin{split}
 V_pi(L)&=1.000000147e^{-L/2}(1+14/(3L))
           +1.78e^{-2L/3}(1+21/L),\
 U_pi(L)&=.9999 e^{-L/2}
                 [1+2(1-e^{(7-L)/2})/L].
end{split}
]
Indeed for the upper bound the logarithmic derivatives are at least
(3/14) and (1/3-2/7=1/21), and for the lower use (t^{-2}ge L^{-2})
on ([7,L]), integrating the square-root main correction exactly.
The local terms apply at every real L, including jumps (Dusart
Prop. 4.3, Cor. 4.5).

Let (M_psi(L)) be the local absolute ψ error from
CH2 Cor. 9.3 (9.4) on ([34,58]), or (D(L)) on (Lge100).
Then (M_psi+W_pi+V_pi) bounds the **lower** normalized error
of (pi) relative to (operatorname{Li}_2), and
(M_psi+W_pi-U_pi) bounds the **upper** one. Compete with
the valid old alternatives. For the upper error from (S_{18})
add (13Le^{-L}+3cdot19!/L^{19}); for the lower error no
addition is needed by the positive remainder. Also retain the
one-sided direct (16Le^{-L}+3cdot19!/L^{19}) upper error
within the inherited sign range. That application is valid throughout
each marked cell since (e^{39.326}<1.2cdot10^{17}).

Insert these tighter errors in the (G_{18}) profile of ramanujan.md,
at each argument separately. Its derivative/negative-tail certificate
works already for (Lge36) (the input to the coefficient inequality
was 36), and the shifted argument satisfies the Li anchor cutoff (L-1ge30).
On a closed cell we use (G_{18}) at the right endpoint, bound the full
nonnegative loss over the cell outward, and subtract the target margin.
We admit only formulas valid over the entire cell at the corresponding
argument; old formulas remain available at source boundaries.
When a cell fails the directed comparison, bisect it with a shared
interior endpoint; fail hard if the proof cannot certify a sufficiently
small cell. gap_repair.py records the number of accepted cells and a strict
lower excess for each claimed interval. This establishes the full union
of cells, not a collection of point samples.

## Proof of the refined tails

For degree n choose (m=n+8), (b=2(m+2)) and use (S_m) in
place of (S_{18}). On (tgemax(100,b)) a common absolute
normalized error for the two sides is
[
 E_m(t)=D(t)+W_pi(t)+V_pi(t)+3t e^{b-t}
                 +2(m+1)!/t^{m+1}.
]
The last two terms are the absolute truncation bound justified in
ramanujan.md. Denote the coefficients of (G_m) by (C_j^{(m)}).
The program proves that the sum of the negative terms at (j>m),
scaled by (L^{m-4}), is strictly below (C_m^{(m)}) at the claimed
onset; it decreases later. Terms with (j>2m) are positive, and
(C_4^{(m)},ldots,C_m^{(m)}>0). Therefore the scaled main-term
reserve (L^{m-5}(G_m-P_n)) is bounded below by
(sum_{j=n+1}^{m-1} C_j^{(m)}L^{m-1-j}), a nondecreasing polynomial.
The exponent (m-5) multiplies the original normalized loss factor
(L^4), so the loss to compare to this polynomial is
[
 L^{m-1}left[rac L{L-1}E_m(L-1)+2S_m(L)E_m(L)+E_m(L)^2
ight].
]
It is nonincreasing on each tested ray. For a term with exponential
(e^{-rt}) and power (t^k) the scaled logarithmic derivative
is at most ((m-1+max(k,0))/(L-1)-r<0) since (kle2, rge1/8)
and (a-1>8(m+1)). The inverse-power loss is decreasing after scaling
as (m+1>m-1). The remaining factors (L/(L-1)), (S_m(L)), and
the unscaled (E_m(L)) are decreasing and positive. The code checks
the comparison at each exact decimal onset, so every later point is
certified. This improves the old use of one reserve coefficient and
a common shifted error: here we retain all terms through (m-1) and
use different errors at the shifted and unshifted arguments.

## Limits and sensitivity

The local ψ and π errors still control the band crossing the end of the
verified PV-li sign input. Extrapolating that sign across the join would
be invalid. The present proof gives a smaller forward-integral cost,
but cannot remove the two local errors; stronger bounds on those or
additional prime counts could tighten these margins. A deeper factorial
truncation reduces the algebraic loss for the high orders, but cannot
remove the dominant exponential density error at the next earlier onset.
In the comparisons, failure of a lower certificate to clear a target
is not a prime-counting counterexample.

All of the finite cells in the first table can be proved without
FKS Cor. 2.9. For the connected fixed margins even if that density
premise is withheld, continue at 60 by the EC-only join [60,269]
in tradeoff.md and then its degree-4 tail; by common.md the exact
direct-ψ assumption used for that tail follows via the density-free
truncation. The sharper higher-order tails in this file use the density
corollary at its stated original-source trust. None of the repairs
attempts to verify the published long finite bridge from scratch.
