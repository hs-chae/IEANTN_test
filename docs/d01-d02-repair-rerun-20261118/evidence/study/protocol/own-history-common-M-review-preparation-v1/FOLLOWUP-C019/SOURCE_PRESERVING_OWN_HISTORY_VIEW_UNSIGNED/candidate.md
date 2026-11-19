# Current D01 repair: both-family portfolio

**Conclusion about additional input.** The mounted contract is FOLLOWUP-D01:
for every real $x\ge e^{200}$,
$|\psi(x)-x|\le x^{7/8}\log^2(x)/64$. This assumption is redundant
over the permitted original inputs B0. The proof below derives the
**exact hypothesis on its full stated real domain** (in fact strictly)
without it. Thus the best defensible strength, onset and connected-domain
frontiers under B0 and B0 plus this input are identical, not merely
indistinguishable at numerical samples. All results below are advances
of the derivations relative to the literal paper formulas, not gains
attributable to the contract. This is not a blind independent baseline run.

**Reading order.** See `ramanujan.md` for the repaired finite comparison,
strict fixed and shaped margins (from $\log x=28.15$ through infinity,
with exact sign onset much earlier), and higher-order and stability
bounds. See `mertens_current.md` for the two products and two sums,
signed curves and finite joins, exact benchmark onsets, and the
power-shaped whole-ray envelopes down to $x=300000$.
`portfolio_check.py` and `mertens_new.py` certify the new analytic
numerical obligations. `restart.md` distinguishes current, historical,
secondary and unfinished results.

## 1. Proving the new assumption from the originals

OpenAIQRH Thm 1.1 (PDF p.4) permits $\beta\le7/8$ for zeta zeros,
*including* possible boundary zeros. No RH or exclusion of the boundary
is inferred. The zero-count and reciprocal-sum references are FKS
Lemma 2.1, Remark 2.2, Cor. 2.3 and Table 1 (PDF pp.4–5). For a cutoff
$T^*<e^y$, $T^*>100$, these give
$2\sum_{0<\gamma\le T^*}1/\gamma < y^2/6+3$: use (U=100),
(S_0<.593), coefficient in (2.1) (<1/6), (2R(100)/100<.1),
and bound the log product by (y^2/2). At (U=H=3\cdot10^{12})
the same coefficient and remainder bounds apply. Reflection
$\beta\mapsto1-\beta$ at fixed positive ordinate shows the subset
$\beta>1/2$ above (H), with conjugates counted, has reciprocal
sum $\le y^2/12+1$. These constants can also be checked by the
short interval tests in `analytic_check.py:test_density` at (U=100,H).
There are no real zeros in (0<s<1): the paired alternating
Dirichlet series for $(1-2^{1-s})\zeta(s)$ is positive there.
Multiplicities are counted throughout.

Use FKS Thm 3.2 (original PDF p.8, signed formula) with
$(\log x_M,\alpha,\omega,M)=(40,1/2,0,2.091)$,
(T=e^{L/4}), $L=\log x\ge200$. Both constraints
$T>\max(51,L)$, (5T+2<e^{L/2}) hold at 200 and thereafter.
Then (T^*\le2.45T<e^{L/4+1}). By QRH a triangle bound, with no
density table, gives
$$
 \frac{|\psi(e^L)-e^L|}{e^L}<
 e^{-L/8}\left(\frac{(L/4+1)^2}{6}+3+
                    2.091 L e^{-L/8}\right).
$$
After division by (L^2) the coefficient in parentheses decreases
and is (<1/64) at 200 (checked in `first_checks`).
This proves redundancy even if no high-strip density table is used.
The original FKS description of the signed formula and its cited
underlying result (Remark 3.3) is retained. The same conclusion also
follows with a wide margin from the screened proof next.

In the opposite direction, the contract alone implies $\beta\le7/8$:
for $\Re s>1$,
$$
 -\zeta'(s)/\zeta(s)=s/(s-1)+s\int_1^\infty(\psi(t)-t)t^{-s-1}\,dt .
$$
The integral is locally normally convergent in $\Re s>7/8$ by
the contract, starting at its actual threshold, with the compact
prefix harmless. Continuation precludes a logarithmic-derivative
pole there. This is an alternative assumption tradeoff if QRH is
not used, **not** a reason to discard QRH in B0. No stronger zero-free
strip follows from this integral at (7/8).

## 2. Sharper original-input power curve

Here is the explicit (C(L)) used in both applications. Set (h=\log H),
(b=7/8), (s_j=.70+j/10000) for (0\le j\le1750).
Use FKS Cor. 2.9, eq. (2.17) and Table 8 (PDF pp.7–8, 26):
(N(s,t)\le c t^{1-\lambda}(\log t)^q+d(\log t)^2),
$\lambda=(8s-5)/3$, (q=5-2s). Take the upward-roundings
((c,d)) encoded in `weights`, `W2`, `params`; at a shared
endpoint the chosen containing interval suffices. In particular
the extra interval [.70,.75] uses (6.173,4.500). This invokes the
stated *interval corollary*, not a re-optimization of Thm 2.7 at
unmatched parameter values. An independent bound with the same powers comes from Dusart Thm 2.3
(PDF p.5), taking $c=4.9\,3^{1-\lambda}$ and $d=51.5$
by $\log(1+w)\le w$. Use the smaller of the **two values**
of $W(s)$ (not separately minimizing $c$ and $d$ across sources).
The positive ordinates with $\beta>s$
exceed (H) by FiniteRH Thm 1 (PDF p.2). The two-sided reciprocal
mass is at most $2\int_H^\infty N(s,t)dt/t^2$. Upon (t=H e^v)
use $(1+v/h)^q\le(1+v/h)^3(1+(q-3)v/h)$ to give the bound
$$
 W(s)=\frac{2c e^{-\lambda h}h^q}{\lambda}
 \sum_{k=0}^{3}{3\choose k}
 \left[\frac{k!}{(\lambda h)^k}
     +(q-3)\frac{(k+1)!}{(\lambda h)^{k+1}}\right]
 +2d e^{-h}(h^2+2h+2).
$$
This bounds the mass with **strict** $\beta>s$ whether the source
counts that or the inclusive set. Define $w_j=\min_{i\le j}W(s_i)$
before the last endpoint, and (w_{1750}=0). For (y=.45L+1) put
$$
 B(L)=\sum_{j=0}^{1749}(w_j-w_{j+1})e^{-(b-s_{j+1})L},\qquad
 C(L)=B(L)+(y^2/12+1)e^{-.175L}
             +(y^2/6+3)e^{-.375L}+2.091 L e^{-.325L}.
$$
Apply the same signed formula now at (T=e^{.45L}), (L\ge180).
The admissibility inequalities hold (in particular (e^{.05L}>6)
and $T>\max(51,L)$). The low half-strip and middle strip
(1/2<\beta\le.70) are bounded by the reciprocal sums above. In
$(s_j,s_{j+1}]$ round up the weight $e^{(\beta-b)L}$;
summation by parts of this increasing weight against cumulative
masses bounded by (w_j) gives (B(L)) for the high strip. The
masses can be restricted to the actual truncated sum without increasing
them. **No missing high-zero tail is added**: the explicit formula
already bounds the difference from the truncated expression.
The rule for (w_j) remains valid even at a discontinuity of the
table bounds. This proves
$$
 |\psi(x)-x|/x \le e^{-L/8}C(L)\qquad (L\ge180).
$$
Term by term (C(L)) decreases there and its limiting coefficient
is $w_{1749}<.00673$. Certified ceilings at $L=180,190,200,250,300,
400,1000$ are .01361, .012902, .012329, .0105496, .0096255, .0086767,
.0073709, respectively. These give whole-ray constants, not merely
point estimates. Dusart Cor. 4.5 turns this into a bound for
$\theta$ by addition of at most $3e^{-L/2}$.
The old D01 .021 coefficient started at 189.5; the new simple
.01361 branch starts at 180 and dominates it on the common ray.
The raw contract is much weaker than either on its whole domain
($L^2/64\ge625$ there). All three facts use $\beta\le7/8$, so
the presence or absence of the contract cannot change the comparison.

The strongest supported curves of this portfolio take pointwise maxima
for lower bounds and minima for upper bounds wherever the individual
premises/domains hold; no claim of global optimality beyond the explicit
fixed-benchmark onsets is made. B0 includes the original QRH theorem,
the original finite numerical trust, and the seven originals at their
actual trust tiers. The comparison with the original-source envelope
uses these same assumptions, not an artificially reduced B0.

**Premise tradeoff:** using Dusart alone in $W$ removes FKS Table 8.
The .01361 simple bound and the same limiting ceiling .00673 hold.
The signed explicit formula and zero-count bounds of FKS are still used;
this is not the density-free alternative of Section 1.
