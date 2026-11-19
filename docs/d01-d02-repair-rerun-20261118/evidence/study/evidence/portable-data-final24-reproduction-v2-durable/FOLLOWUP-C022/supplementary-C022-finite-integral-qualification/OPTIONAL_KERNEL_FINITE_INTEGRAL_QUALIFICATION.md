# C022: finite-integral qualification of the optional general kernel lemma

The actual written identity is `D02.M.general-kernel`, D02_M.md physical LF197–233 (SHA-256 d9e279f13288e2a807d0894c0d62fc21dfb7a6b9040207f284fda4e943911fd4). No standalone Blueprint label or Lean declaration exists for this written construction. The original generic conditions are nonnegative decreasing differentiable f and a vanishing boundary product. The raw generality is incomplete: they do not ensure a finite improper integral. That original wording and the fresh review's finding remain immutable.

This is an internal partial-summation deduction. No permitted original paper is claimed to state this exact general lemma. Its source input is a lawful uniform theta-error majorant, instantiated from the source bounds at their actual domains (in particular Dusart Theorem4.2, PDFpp11–12; and the separately proved eligible theta envelopes). The abstract input and the required extra calculus condition are

\[
 |\theta(t)-t|\le d(y)t\quad(t\ge y),\qquad
 I_f(y)=\int_y^\infty f(t)\,dt<\infty.
\]

The counterexample to the unqualified formulation is f(t)=1/(t log t) on t≥2: t f(t) tends to zero, but its integral diverges. Its displayed absolute difference is therefore not an inequality between real quantities. This is a scope defect in the generic lemma, not a counterexample to a current Mertens bound.

For the corrected statement keep all original conditions and require the finite integral above. The actual proof is complete as follows. Use the positive Stieltjes measure d(-f); this also avoids needing an unstated absolute-continuity assumption for the general derivative notation. Abel summation and the vanishing boundary give

\[
 \sum_{p>y}\log p\,f(p)
 =-\theta(y)f(y)+\int_y^\infty\theta(t)\,d(-f)(t).
\]

Integration by parts gives

\[
 \int_y^\infty t\,d(-f)(t)=yf(y)+I_f(y).
\]

Both sides are finite under the stated conditions, and the theta majorant bounds the prime sum absolutely. Subtract the corresponding identity with theta(t) replaced by t. Its boundary error is at most d(y)y f(y), and its integral error is at most d(y)[y f(y)+I_f(y)]. Hence

\[
 \left|\sum_{p>y}\log p\,f(p)-I_f(y)\right|
 \le d(y)\bigl(2yf(y)+I_f(y)\bigr).
\]

For the actual smooth kernels this measure is exactly -f'(t)dt. Every kernel in the author's k=2,3 applications satisfies the finite-integral condition, without a new analytic premise or changed numerical output. For y>1,

\[
 \int_y^\infty t^{-k}\,dt=\frac{y^{1-k}}{k-1}<\infty,
 \qquad k\ge2,
\]

\[
 0\le\int_y^\infty\frac{dt}{kt^k\log t}
 \le\frac{y^{1-k}}{k(k-1)\log y}<\infty.
\]

The root arguments in those applications are positive and greater than one; each theta majorant still needs its own previously proved source eligibility there. This qualification adds no source estimate, changes no algorithm/parameter/output, and leaves every current numerical enclosure and ANT consumer unchanged. The raw unrestricted generic statement is not admitted. Only this explicitly qualified theorem and its already convergent applied kernels are admitted. This written proof is not a Lean theorem, source-first PV or a new verified network premise.
