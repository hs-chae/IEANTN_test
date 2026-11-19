# C020: a finite margin was incorrectly promoted to a whole ray

This corrects one mathematical scope error in the original C020 review and
Root finalization. Those original files remain immutable. The mathematical
source, algorithms, parameters, numerical outputs and experimental history
are unchanged. This is supplemental informed adjudication, not a new blind
discovery or a retroactive primary success.

## Actual written declaration and implementation

There is no standalone Blueprint label or Lean declaration for this written
experiment. The identity is C020, `R-stronger-constant-3`,
`finite_anchor.md`, physical LF48. Put
\[
 L=\log x,\qquad
 R(x)=\frac{ex}{L}\pi(x/e)-\pi(x)^2,\qquad
 Y(L)=\frac{L^6R(e^L)}{e^{2L}}.
\]
The source lists a margin 1.03 at the old log onset 30.75, and then says the
common tail uses
\[
 Y(L)>1+\frac{14}{L}+\frac{16}{L^2}\qquad(L\ge191).
\]
The source's actual `ram_repair.py`, LF208–219, separates `EXTRA` finite
rows from `EXTRA_TAILS`. Its row is exactly
`('30.75',191,4,'1.03')`; LF194–195 defines this as the constant
profile on the finite closed interval. The complete original exact
`ram_repair` replay checked that row. The earlier review instead recorded
the 1.03 margin on the unbounded ray, and Root admitted that overstatement.

## Primary-source correspondence

No original paper in the permitted corpus asserts the decimal 1.03 on this
ray. It is a project-derived profile, assembled from the eligible original
prime-count bounds. The relevant high-range source is the original QRH
Theorem 1.1, together with FKS Theorem 3.2 and its lawful first-panel density
input, as already pinned in C020's complete source audit. OpenAI QRH
Theorem 1.1, PDF p.4, physical text LF255–262, gives the closed upper
zero cap
\[
 \mathop{\rm Re}\rho\le\frac78.
\]
FKS Theorem 3.2, PDF p.8, physical LF631–642, at its
\((\log x_M,\alpha,\omega,M)=(40,1/2,0,2.091)\) row, gives a height
\(T^*\in[T,2.45T]\) with
\[
 \left|\psi(x)-x+\sum_{|\gamma|\le T^*}\frac{x^\rho}{\rho}\right|
 \le \frac{2.091x\log x}{T},
 \qquad \log x\ge40,\quad \max(51,\log x)<T<\frac{\sqrt{x}-2}{5}.
\]
Choosing an exponential height and using the reciprocal-zero sum bound
therefore yields a power-saving prime-count error. These source inputs,
followed by the standard repeated
partial-summation expansion used in C020 is
\[
 A(L):=Le^{-L}\pi(e^L)
 =1+\frac1L+\frac2{L^2}+\frac6{L^3}+\frac{24}{L^4}
  +O(L^{-5}).
\]
This is a consequence of those source inputs; it is not a quotation of a
paper's 1.03 theorem. The exact source locations and hashes remain in the
unchanged original review and source manifest.

## Concrete flaw, consequence and correction

The finite row cannot inherit the constant of an unrelated analytic tail.
The displayed tail decreases to 1 and is less than 1.03 for sufficiently
large log arguments. More decisively, the actual arithmetic quantity has
limit 1. Indeed,
\[
 Y(L)=L^4\left(\frac{L}{L-1}A(L-1)-A(L)^2\right).
\]
The coefficients through inverse-log degree four in the two terms are
respectively
\[
 (1,2,5,16,65),\qquad(1,2,5,16,64).
\]
Consequently
\[
 Y(L)=1+O(L^{-1}),\qquad\lim_{L\to\infty}Y(L)=1.
\]
Thus a constant lower margin greater than 1 cannot hold on any final
unbounded ray. The later same-arm D02 author additionally supplied a
specific upper bracket at log argument 1000 and an improved finite
interval; their independent review is separate and is not needed to
justify this correction.

The admitted original-profile branch is now explicitly
\[
 Y(L)>1.03\qquad(30.75\le L\le191).
\]
This uses the unchanged original finite certificate and proof. Every other
accepted original C020 branch, including the entire analytic tail and all
143 prior targets, is retained. Taking the maximum with those other
branches can imply further finite coverage; it does not restore an
unbounded constant 1.03 assertion. The later D02 interval is not imported
retroactively into the D01 portfolio. The raw original review and wrong
global domain remain available alongside the explicit corrected domain.

There are still 294 admitted scoped objects, with this one admitted only
at its corrected finite scope. They are not 294 independent discoveries
or 294 supported raw unqualified assertions. This distinction must enter
the machine frontier data, family summary, inherited-floor comparison and
final report. Full analytic Lean and source-first PV remain unestablished.
