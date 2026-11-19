# Common-original implication of the additional input

Write \(B_0\) for the cumulative original-paper premises at their
supplied trust, and \(L=\log x\). On **every real** \(x\ge e^{200}\),
these premises alone imply
\[
 \frac{|\psi(x)-x|}{x}\le e^{-L/8}d(L),\qquad
 d(L)=\frac{.0106 L}{L-92}
      +(.01L^2+1.865)e^{-3L/40}
      +2.091 L e^{-L/8}.
 \tag{D}
\]
The function \(d\) decreases there, and \(d(200)<.021,\ d(250)<.017,\
d(300)<.016,\ d(800)<.012\). In particular the exact supplied
hypothesis (with its \(1/64\), \(L^2\), and real onset \(e^{200}\))
follows from B0: \(d(L)<.021<625\le L^2/64\).
This compares attainable theorems with matched premises, not
just isolated estimates. Every theorem from B0+D01 has a B0
proof by substitution of this lemma. Neither family can have
a genuinely additional improvement in that trust model.
Nothing here says D01 is proved with QRH *excluded*.

## Proof and exact source dependencies

1. OpenAIQRH Theorem 1.1 (PDF p.4) explicitly includes \(\zeta\);
   \(\beta\le7/8\) for nontrivial zeros, not \(\beta<7/8\).
   Platt–Trudgian FiniteRH Theorem 1 (PDF p.2) verifies RH through
   \(3000175332800\); take \(H=3\cdot10^{12}\). There are no real
   nontrivial zeros: paired terms of \(\sum (-1)^{n-1}n^{-s}\)
   are positive for real \(0<s<1\); by locally uniform
   convergence of the paired series on \(\Re s>0\) it equals
   \((1-2^{1-s})\zeta(s)\) there. No zero with \(0<\gamma\le H\) belongs to
   the right strip used below.
2. Use FKS Theorem 3.2 (PDF p.8), **not** its Theorem 3.1. Choose
   the printed admissible tuple
   \((\log x_M,\alpha,\omega,M)=(40,1/2,0,2.091)\).
   Put \(T=e^{L/4}\). For \(L\ge200\),
   \(\max(51,L)<T<(e^{L/2}-2)/5\); the inequalities hold at 200
   and remain true by monotonicity of \(e^{L/4}/L\) and
   \(e^{L/4}-2e^{-L/4}\). The formula holds for all real \(x\):
   the sum through some \(T^*\in[T,2.45T]\) has remainder at most
   \(2.091xL/T\). This avoids extension from half odd integers and
   the issue noted in FKS Remark 3.3 about earlier truncated formulas.
3. For zeros \(\beta<.8\), bound \(1/|\rho|\le1/|\gamma|\) and use
   Platt–Trudgian 1809.03134v2 Lemma 2 (PDF p.4), including
   multiplicity and both signs. Since \(0<\log(T^*/(2\pi))<L/4\),
   their normalized absolute sum is at most
   \(e^{-.2L}(.01L^2+1.865)\).
4. For \(.8\le s\le.875\), FKS Corollary 2.9, (2.17), PDF pp.7–8,
   and Table 8, PDF p.26 (rows [.80,.81] through [.87,.88]), bound
   \(N(s,y)=\#\{0<\gamma<y,\ \beta\ge s\}\), for \(y\ge H\), by
   \[
    11.076\,y^{(8/3)(1-s)}(\log y)^{5-2s}+3.693(\log y)^2.
   \]
   Both decimal caps round upwards from all applicable
   \(\widetilde c_1,\widetilde c_2\) entries; we use the published
   table bounds at their original trust. Set
   \(h=\log H,\ a(s)=1-(8/3)(1-s),\ q(s)=5-2s\).
   Positivity of the zero count gives
   \[
    S(s):=2\sum_{\beta\ge s,\ \gamma>0}\frac1\gamma
      =2\int_H^\infty \frac{N(s,y)}{y^2}\,dy
      \le B(s)
      :=2\left(\frac{11.076\,h^{q(s)}e^{-a(s)h}}{a(s)-q(s)/h}
            +\frac{3.693(h^2+2h+2)}H\right).
   \]
   For the first integral in \(u=\log y\), use
   \(u^q\le h^q e^{(q/h)(u-h)}\) for \(u\ge h\). The denominator
   is positive already at \(s=.8\), where it is \(7/15-3.4/h\).
   The magnitude of the negative log derivative of the first
   summand in \(B(s)\) is at most
   \[
     (8/3)h+2\log h+\frac{8/3+2/h}{7/15-3.4/h}<92.
   \]
   Its other summand is constant. Consequently
   \(S(s)\le .0106\,e^{92(.875-s)}\), using \(B(.875)<.0106\).
   The numerical checks for \(B\), its derivative bound and \(d\)
   use exact intervals in `verify.py`.
5. Each zero with \(\beta\ge.8\) has
   \(e^{L(\beta-1)}=e^{-.2L}+L\int_{.8}^{\beta} e^{L(s-1)}\,ds\).
   Bound the truncated absolute sum by the full weighted count.
   Insert the bound for \(S\) and integrate to obtain
   \[
    .0106\,e^{-L/8}\left(e^{-.075(L-92)}
       +\frac L{L-92}(1-e^{-.075(L-92)})\right)
      \le .0106\,e^{-L/8}\frac L{L-92}.
   \]
   This includes zeros on both cutoff lines. Add the low band
   and remainder to obtain (D). All three terms of \(d\) decrease
   at and beyond 200 (differentiate the exponential monomials).

The tail removes two log powers from D01 at the same exponent and
onset, and avoids the finite-height bound's constant relative floor.
The limiting coefficient .0106 is not a lower bound. Better density or
cancellation estimates near the QRH boundary could further improve it.
