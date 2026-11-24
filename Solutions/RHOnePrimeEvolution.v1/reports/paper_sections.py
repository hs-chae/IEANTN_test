"""Short mathematical exposition; the published analytic inputs remain explicit."""
SUMMARY_FORMULAS={
 'SP_objects':r'f(x):=\sqrt x\log x,\quad \pi(x):=\#\{p\le x:p\text{ prime}\},\quad p_n:=\operatorname{Nat.nth}(\operatorname{Prime},n),\quad p_0=2.',
 'SP_objective':r'\frac{\int_{\mathbb R}|F(x)|\,dx}{F(0)-(36/11)\int_{|t|>1}\max\{G(t),0\}\,dt}\le\frac{834021}{1000000},\qquad F(0)-(36/11)\int_{|t|>1}\max\{G(t),0\}\,dt>0.',
 'SP_gap':r'\forall\varepsilon>0\ \exists N\ \forall n\ge N:\qquad\frac{p_{n+1}-p_n}{\sqrt{p_n}\log p_n}\le0.834021+\varepsilon.',
 'SP_population':r'\begin{gathered}\alpha\ge0,\quad\varepsilon>0,\quad c=0.834021(1+2\alpha)+\varepsilon:\\\exists X\ \forall x\ge X,\qquad\pi(x+cf(x))-\pi(x)>\alpha\sqrt x.\end{gathered}',
}
def render_summary(lang,m,link,source):
    return ''.join([
      '<section id="summary"><h2>A certified Gaussian Fourier witness and conditional prime bounds</h2>',
      '<p>A rational polynomial–Gaussian witness gives a smaller asymptotic prime-gap coefficient than the specific 2026 printed benchmark examined here. We prove its actual Fourier identity and whole-integral numerical bounds in Lean, then apply the published CMS analytic reductions, which remain explicit mathematical inputs to the Lean consumers. Ordinary RH is required; GRH is not substituted for it.</p>',
      m('SP_objects'),m('GF_functions'),m('SP_objective'),
      '<p>The witness uses thirteen rational search coefficients. A proved polynomial-Gaussian Fourier recurrence identifies its transform exactly. A general certificate soundness theorem, exact rational polynomial integration, exponential remainder bounds and genuine infinite tails establish the norm and positive-leakage bounds. The optimizer and external certificate generator are untrusted producers; their suggested data acquire mathematical force through the kernel proofs.</p>',
      '<p>Under RH and the stated CMS functional source inputs, the numerical witness yields both of the following conclusions. The count in the second display includes the upper endpoint.</p>',
      m('SP_gap'),m('SP_population'),
      '<p>The first result also proves that the normalized gaps are eventually strictly below the reviewed coefficient 0.834050619151. Neither conclusion supplies an explicit onset. The population curve improves the older displayed CPJ curve 0.8358(1+2α), while newer population estimates can be stronger in other regimes. No global best-known-result or optimality claim is made.</p>',
      '<p>A separate CMS cosine-kernel construction retains the explicit strictly open frontier below, with a stronger continuous endpoint in the full report. A separately named historical gap-table premise supplies an absolute-width 1551 finite bridge down to exp(24); that computation is not newly verified.</p>',
      m('OP_uniform'),
      '<p>Two further consumers use the unchanged octic RH/Green/Nicolas/BPT package. A disjoint variable-width partition gives the cube count below at the original onset, including the concrete natural onset 2981. Recovering logarithmic count slack also saves 4.725 times the square root of the starting point in the corresponding prime-index window, with indices measured as offsets after the number of primes at or below that point.</p>',
      m('NET_cube_density'),
      '<p>A sorting-fiber argument permits two or three selected primes per ternary representation. With the same inherited analytic package and the explicit finite binary-Goldbach hypothesis, it yields the following newly covered band for this transfer.</p>',
      m('NET_goldbach_numeric'),
      '<p>All final numerical and mathematical consumers have kernel proofs with only the standard Lean axioms. The published CMS and inherited analytic predicates are not newly derived from Mathlib RH. These are kernel mathematical and certificate proofs, not source-first C/C++/CUDA program verification. Tighter external Gaussian and rational-hat numerical results remain separate experimental evidence.</p>',
      '<p class="source-links">',source('https://arxiv.org/pdf/1708.04122v2#page=5','CMS Theorem 3 / Corollary 4'), ' · ',source('https://zenodo.org/records/24429650','Blanquer Robles 2026, v2'), ' · ',link('Solutions/RHOnePrimeEvolution.v1/ONE_PRIME_AND_NETWORK_THEOREM_MATRIX.md','Exact theorem matrix'),'</p></section>'
    ])
