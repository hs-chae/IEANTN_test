# A-D01 — explicit prime-counting, Mertens, and arithmetic consequences

All logarithms natural. Statements are for real arguments with inclusive prime counting, unless explicitly about integers. We assume the original theorems in the packet, with their original trust status. We do **not** assume full RH. In particular, the power estimates below use the admitted original **OpenAIQRH Theorem 1.1**, not an implication from finite-height RH to full RH or a bound for the line β=7/8 strictly excluding zeros. Either the original QRH theorem for ζ or the extra hypothetical PsiMajorant suffices for the zero-free hypothesis in the principal results (see direct proof below). No new non-packet analytic facts about primes are assumed.

## Results (see also mertens.md and arithmetic.md)

1. **Ramanujan quantitatively.** With L=log x, the new two-sided, pointwise bound (R1) below applies for L≥30.5. In particular
   * R(x)>.04 x²/L⁶ for L≥30.5;
   * R(x)>.30 x²/L⁶ for L≥31;
   * R(x)>.70 x²/L⁶ for L≥32;
   * R(x)>x²/L⁶ for L≥33.2;
   * R(x)>(1+14/L+2/L²)x²/L⁶ for L≥48. The additional nested polynomial margins are stated in Section 2.
   These are one family of correlated margins, not independent estimates. The strongest pointwise lower bound may be taken as the maximum of (R1) and the applicable simple margins.
2. **Optimal real sign endpoint, with inherited computation.** Let N=38,358,837,682. There is a unique α∈(N+.2179263651446,N+.2179263651448) solving
   e α · 632207037/log α = 1644673232².
   For all real x>α, R(x)>0; at α, R(α)=0. Only the small baseline interval at integers uses PT Theorem 2 (the portion from N+1 through exp(58)); the new analytic proof independently covers exp(30.5) onwards. The use of PT can be reduced to integers below exp(30.5)+1. See endpoint.md for an endpoint caveat.
3. **Power improvement upstream.** For L≥190,
   |ψ(x)−x|≤ F(L)x^(7/8) < .019535 x^(7/8), and |θ(x)−x| < .01955 x^(7/8). F is given below, is decreasing, and is <.013604 at L=400. The improvement over the extra input on the latter's entire ray is at least a factor 625/.019535>31,990, growing without bound. The start is exp(190), not exp(200). If desired all older estimates (CH2 globally, FKS, PT and Dusart at their stated ranges, the input majorant when assumed) can still be taken in pointwise minima; none are taken to cease to hold.
4. **Mertens**: whole-ray hybrid envelopes for both reciprocal Euler products and both prime sums, with old bounds retained pointwise, in mertens.md and the signed strengthening (S2) in smooth.md. **Tertiary arithmetic**: short intervals in arithmetic.md; primorial positivity up to exp(84.5), far-ray primorial errors and general integer bounds in smooth.md.

## Original-source locators and trust
* /task/INPUT_CONTRACT.json: PsiMajorant, explicitly hypothetical.
* /corpus/originals/OpenAIQRH.pdf, PDF p.4 Thm. 1.1: Re ρ≤7/8. Used as an admitted analytical theorem, not newly formalized or independently checked here.
* /corpus/originals/FKS.pdf, PDF p.8 Thm. 3.2, admissible parameters (log x_M, α, ω, M)=(40,1/2,0,2.091). Cited Cully-Hugill–Johnston explicit formula as admitted in FKS; **not** FKS Prop. 3.4 or the earlier Dudek formula, which FKS Remark 3.3 flags. Cor. 2.9 (PDF p.7), Table 8 first block (PDF p.26; a1=.77), and PDF p.4 definition of N(σ,T). These keep the paper's analytical and numerical trust status.
* /corpus/originals/PlattTrudgianFiniteRH.pdf, PDF p.2 Thm. 1 (rigorous interval computation of RH to height 3000175332800). We only need H=3·10^12. PT Lemma 4 (below) also provides this range including γ=0. FKS takes (1.7) as an input.
* /corpus/originals/CH2.pdf, PDF p.2 Cor. 1.3: both |ψ(x)−x|/x and |sum_{n≤x} Λ(n)/n−log x+γ| bounded by π/(3·10^12)+113.67/√x for x≥1. Original analytical/computational result; used at its stated trust. The exact ratio π/(3·10^12) matters.
* /corpus/originals/PlattTrudgian1809.03134v2.pdf (PT): Lemmas 2 and 4 p.4; Thm. 2 p.3; Lemma 6 pp.9–10; π-error bound quoted in last paragraph p.8, and normalization Eq. (11) p.7. The π-error quotation is cited with an additive allowance of 2 (unnecessary for the literal normalization in PT). All keep original-source trust, including the finite computations.
* /corpus/originals/Dusart2018.pdf: Cor. 4.5 p.13 gives 0≤ψ−θ< (1+1.47·10^−7)√x+1.78 x^(1/3). Thms. 5.6–5.7 pp.17–19 (constants, identities, baselines), Thm. 5.9 pp.19–20. These keep the original trust.
* /corpus/originals/DudekPlatt1407.1901v1.pdf: Thms. 1.2, 1.3 p.2, asymptotic cancellation pp.2–3; never use full-RH conclusion as a premise. The supplied native source `/baseline/ieantn-source/IEANTN/Nodes/DudekPlatt/v3/Conclusions.lean` documents a sign defect in the original criterion for negative m; our exact two-sided computation does not use that criterion. The supplied DPv3 solution and receipt verify the *repaired conditional implication*, not the new results. No imported numeric table except where explicitly cited from an original.

## Alternative zero-free premise from the hypothetical input
On Re s>1, Euler product differentiation and partial summation give
`−ζ'(s)/ζ(s)=s/(s−1)+s∫_1^∞(ψ(u)−u)u^(−s−1)du`.
The integral is holomorphic throughout Re s>7/8 under PsiMajorant (absolute, locally uniform convergence; the initial finite interval is harmless). The identity continues meromorphically there; one can use ζ(s)=s/(s−1)−s∫_1^∞{u}u^(−s−1)du on Re s>0 for the continuation. A zero would force a pole of the logarithmic derivative, so there is none in that open half-plane. This replaces the use of QRH Thm. 1.1 everywhere in this study if one opts to assume PsiMajorant instead. Conversely Section 1 with the original QRH input already implies PsiMajorant with plenty of slack; the hypothetical estimate is not claimed to be a literal original-paper theorem.

## 1. A power bound with explicit coefficient function
Write Dψ(t)=(ψ(e^t)−e^t)e^−t, and similarly Dθ. For s>.5 define W(s)=2∑_{γ>H, β≥s} 1/γ with multiplicities. FKS counts σ≤β (inclusive), so this method also handles zeros on the boundary. For r=(8s−5)/3, q=5−2s, z=log H, and a permissible pair (c,d) from FKS, we have
```
W(s) ≤ 2[c exp(−r z) z^q/(r−q/z) + d exp(−z) z²/(1−2/z)] .    (P0)
```
This holds where both denominators are positive. Proof: integrate N(s,u)/u² for u≥H, by Tonelli applied to the individual 1/γ weights (or Stieltjes partial summation, boundary at ∞ zero). Substitute u=e^v and use v^q≤z^q exp(q(v−z)/z) for v≥z. The same bound with z=log Y applies to the sum over γ>Y≥H: dropping the negative boundary at Y only enlarges the bound.

Use the sorted mesh s_j (in units 10^−4) and W upper bounds w_j (in units 10^−6) in weights.txt. They are generated and checked via exact rational bounds in cert.py, taking running minima because W is nonincreasing. Let s_{m+1}=7/8, with j=0,...,m the actual rows; s_0=.70. On t≥40 define
```
C(t)=(t/3+1)^2/6+2,
F(t)= C(t)e^(−.175 t) + 2.091 t e^(−5t/24)
      + w_m + sum_{j=0}^{m−1}(w_j−w_{j+1}) e^((s_{j+1}−7/8)t).
```
Apply FKS Thm. 3.2 with T=e^(t/3). Its conditions max(51,t)<T<(e^(t/2)−2)/5 hold at t=40 and remain true by exponential growth, e.g. e^(t/6)>6 and e^(t/3)>2. The truncation height T*≤2.45T<eT and PT Lemma 2 give total reciprocal-zero weight ≤C(t), using 2π>6 and 2·.9321<2. Conjugate zeros contribute equally to the absolute estimate; PT Lemma 4 excludes a real noncritical zero, and FKS's explicit sum and zero sum use the usual nontrivial zeros (see note on the real axis below). The zeros with β<.70 contribute at most C(t)e^(−.30t). The others have γ>H (positive side). Majorize e^((β−1)t) by the upper staircase with values e^((s_{j+1}−1)t) for β between s_j and s_{j+1}; the differences of successive staircase heights are nonnegative. Summing with the cumulative w_j and telescoping gives precisely the remaining mesh terms in F(t) times e^(−t/8). The explicit-formula remainder is 2.091t e^(−t/3). Thus |Dψ(t)|≤F(t)e^(−t/8). Every summand of F(t) is constant or decreasing for t≥40 (use the logarithmic derivative bound 2/(t+3) on C), hence the endpoint evaluations are whole-ray certificates. Dusart Cor. 4.5 yields the asserted θ bound.

Real-axis detail if needed: for 0<s<1, the alternating Dirichlet series η(s)=∑(-1)^(n−1)n^−s is positive (group pairs). The relation η(s)=(1−2^(1−s))ζ(s) holds for Re s>1 by absolute convergence and extends to Re s>0 off s=1 by the identity theorem and uniform convergence on compacta via summation by parts. Thus no real nontrivial zero, including at s=.5.

## 2. Explicit approximation and Ramanujan margin
Write S(t)=∑_{k=0}^{12} k!/t^(k+1), A(y)=y S(log y), and D=1.048·10^−12, P=.01955. The elementary inequalities 25/8<π<3.144 follow, for example, from the alternating arctangent series in Machin's identity (by tangent addition); cert.py checks them. In particular CH2 and Dusart give |Dθ(t)|≤D+116e^(−t/2) for t≥22 (116 is rounded up). For t≥190 the new θ bound also gives |Dθ(t)|≤P e^(−t/8).

For t≥29.5 let B(t) be the minimum of the following eligible positive expressions, with K=13!:
```
B_G(t) = 10000e^−t + [D(1+2/t)+116(1+3/t)e^(−t/2)]/t + 3K/t^14   (all t);
B_I(t) = (1.95+3.9/t+19.5/t²)e^(−t/2)/t + 8e^−t + 4K/t^14          (t≤43.7);
B_H(t) = 10000e^−t + (t+2)e^(−t/2)/25 + 3K/t^14                    (t≤58);
B_P(t) = 10000e^−t + (2D+348e^−95)/190² * e^(190−t)
          + P(1+2/t)e^(−t/8)/t + 3K/t^14                           (t≥190).
```
We prove |π(e^t)e^−t−S(t)|≤B(t).
* A'(y)=1/log y−K/(log y)^14. With a=e^22, partial summation gives the difference π−A at y as the sum of (θ(y)−y)/log y, the anchor constant C0=π(a)−θ(a)/22−A(a)+a/22, and the integral from v=22 to v=t of e^v[Dθ(v)/v²+K/v^14]. This identity is right-continuous at all jumps. For C0 subtract the smooth main at b=600. At b the difference (π−θ/log)(b)−Li_2(b)+b/log b has magnitude <2000: 0≤π−θ/log≤600, Li_2(600)≤598/log2<1000, and 0<b/log b<600. By PT Lemma 6 the intervening error integral from log b to 22 has absolute value ≤2e^11/(8π)<5000. The final difference Li_2(e^22)−A(e^22) is <50 by the Li anchor test below. Hence |C0|<10000.
* On t≥22 the derivative of e^v/v^14 is at least e^v/(3v^14); analogous derivative ratios for e^v/v² and e^(v/2)/v² are ≥1/2 and ≥1/3 respectively. Integrate and drop the nonnegative primitive at the lower endpoint: B_G follows. PT Lemma 6 gives local bound t² e^(−t/2)/(8π), and the error integral is then at most 2 e^(t/2)/(8π); this gives B_H. For B_P, integrate the global error up to v=190 and the pure power thereafter; the derivative ratio of e^(7v/8)/v² from 190 is ≥1/2. The factorial remainder is unchanged.
* B_I follows instead from the quoted PT bound for π against Li, on the safe subrange t≤43.7 (e^43.7<10^19), plus 2 for any change from the paper's normalization to Li_2(y)=∫_2^y dt/log t. The ancillary certificate gives 0<Li_2(e^20)−A(e^20)<6. Use the derivative ratio e^v/v^14 ≥ itself times 1/4 after differentiation, for v≥20. The same anchor plus the integral up to 22 verifies the bound <50 used above. Exact anchors use the positive expansion log(t/log2)+∑_{j≥1}(t^j−(log2)^j)/(j j!) for Li_2(e^t).

Then for L≥30.5 (no sign worry because π,S nonnegative),
```
D0=S(L−1)/L−S(L)^2,
ε0=B(L−1)/L + [2S(L)+B(L)]B(L),
x²(D0−ε0) ≤ R(x) ≤ x²(D0+ε0).                                   (R1)
```
Indeed the π(x/e) expression scales by 1/L, and |a²−b²|≤|a−b|(2b+|a−b|). The binomial series in 1/L gives
`L^6 D0 ≥ ∑_{j=4}^{18} c_j L^{4−j}`, where
`c_j=∑_{k=0}^{min(j,12)} k! binom(j,k) − ∑_{k=max(0,j−12)}^{min(j,12)} k!(j−k)!`.
To see this, keep all nonnegative shifted terms through j=24; there are no square terms after that. c_0,...,c_3=0 and the next four coefficients are 1,14,145,1412. Terms j=4..18 are positive, and the sum from j=19 to 24 is nonnegative for L≥30.5 by lower-bounding its bracket after factoring L^−19 at L=30.5 (retain c_19, bound each negative contribution there). Coefficient arithmetic is checked exactly.

In ram.py, each rational cell [u,v] uses the deterministic polynomial at v. For each separately eligible branch over the whole cell, its B is decreasing and bounded by its value at the left endpoint; e.g. a branch requiring t≤58 is only used if the right endpoint satisfies it. Thus `v^5 Bcell(u−1)+v^6(2S(u)+Bcell(u))Bcell(u)` bounds L^6 ε0 uniformly, not just on a grid. On [48,191] test after subtracting 1+14/L+2/L² and multiplying by L². For L≥191 it suffices to use B_P for both errors: `L^7 B_P(L−1)` and `L^8 B_P(L)` are decreasing termwise (exponent rates at least 1/8, factorial remainder power 14), and `2S+B_P` also decreases. The scaled loss at 191 using B_P is <143, proving the last margin for the rest of the ray. All comparisons are strict by certified positive slack.

More polynomial coefficients: for each (q,A)=(3,223),(4,257),(5,292),(6,327),(7,363),(8,408), and every L≥A,
```
R(x) > (x²/L⁶) ∑_{j=4}^{q+3} c_j/L^(j−4).
```
The same monotonicity proof applies to L^q times the loss L^6ε0 with B_P (the factorial-remainder exponent is 14≥6+q and the exponential rates are ≥1/8). At A its value is <c_{q+4}, verified exactly in ram.py. The positive deterministic polynomial keeps that next coefficient to pay for the error. In particular the coefficients 145, 1412, 13985, 145450, 1610021 and 19063832 successively enter the lower margin at the displayed onsets.

**Comparison:** This fills the entire gap between the two PT intervals (even without PsiMajorant), and provides at least (1+14/L+2/L²)x²/L⁶, not merely positivity, at every point of PT's upper ray. It gives a strictly positive certified margin beginning well before exp(58). The small real endpoint issue is addressed without turning a false real statement into an inference rule.

## Reproduce and status
Run with /usr/bin/python3.10 -B cert.py and /usr/bin/python3.10 -B ram.py, in this directory. Their only logarithm/exponential intervals are Taylor/atanh rational bounds, with diagnostic floats used for display only. The integer sieve details and run commands are in the companion files. Mathematics is a supported argument plus the inherited original numerical inputs as named; no kernel proof or source-first PV of an original computational result is claimed. The exploratory notes distinguish old attempts and open directions from supported results.
