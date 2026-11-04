# Ramanujan forward pilot: what is proved, why the program proves it, how to check it

This page is for a reader trained in mathematics who has not seen the C or Lean source. It covers
the nodes `RamanujanNumerics.v1`/`.v2` (the numerical budgets) and `RamanujanGap.v1`/`.v2` (the
prime-counting consequences), together with their inputs `DudekPlattNumerics.v7` and `.v5`. The
statements themselves are in each node's `Conclusions.lean`. This page explains them and does not
replace them. The old nodes are frozen, which is why the explanation lives here and not in their
docstrings.

**Status in one line.** On the whole ray $x>e^{3915}$ the program-checked allowance for the
normalized Ramanujan shortfall drops from $3914.7/\log x$ to $9.101/\log x$. This is a controlled
replay of an input already known to be valid. It is not a best-known bound, and it is not
officially verified (no receipt). Each numerical certificate depends on six finite `native_decide`
facts. The analytic input remains an explicit premise.

---

## Depth 1: the claim

### The quantity

With $\pi$ the prime-counting function, Ramanujan's inequality is
$\pi(x)^2 < \frac{e x}{\log x}\,\pi(x/e)$. The nodes define

$$
\operatorname{gap}(x)=\frac{e\,x}{\log x}\,\pi\!\left(\frac{x}{e}\right)-\pi(x)^2,
\qquad
\operatorname{loss}(x)=\max\!\Bigl(0,\;1-\frac{(\log x)^6}{x^2}\operatorname{gap}(x)\Bigr)
$$

(`RamanujanGap.v1.gap`, `RamanujanGap.v1.loss`; the later versions reuse them unchanged). The
leading asymptotic size of the gap is $x^2/(\log x)^6$. The loss is therefore the shortfall from
that leading size, normalized and clipped at 0, so $\operatorname{loss}(x)<1$ forces
$\operatorname{gap}(x)>0$.

### Hypotheses and domains

The analytic input is a two-sided expansion of $\pi$ around the main term
$S_5(x)=x\sum_{k=0}^{4}k!/(\log x)^{k+1}$ (`DudekPlatt.v3.mainTerm`). It is needed **on two
different ranges**:

| Input | Lower half | Upper half | Status |
|---|---|---|---|
| Old, `DudekPlattNumerics.v7.pi_asymmetric_pnt` | $S_5(x)-1194\,x/\log^6x<\pi(x)$ for $x>e^{3914}$ | $\pi(x)<S_5(x)+1426\,x/\log^6x$ for $x>e^{3915}$ | Source premise from PNT+ at `c39a751`, not replayed |
| New, `DudekPlattNumerics.v5.pi_two_sided_qrh` | $S_5(x)+119\,x/\log^6x<\pi(x)$ | $\pi(x)<S_5(x)+131\,x/\log^6x$ | Both halves for $x>e^{400}$. Proved in Lean from `QRHCH2.v5.psi_refined_bound`, which needs 13 named CH2 premises and the QRH theorem |

The two ranges differ because the lower half is applied at $x/e$ while the upper half is applied at
$x$. The old input's ranges $e^{3914}$ and $e^{3915}$ are kept exactly as the source states them
(`FORWARD_PROTOCOL_AMENDMENT_1.md`).

### Conclusions, old and new

| | Old (`RamanujanGap.v1`) | New (`RamanujanGap.v2`) |
|---|---|---|
| `loss_bound` | $\operatorname{loss}(x)\le 3914.7/\log x$ | $\operatorname{loss}(x)\le 9.101/\log x$ |
| `gap_lower_bound` | $\bigl(1-\tfrac{3914.7}{\log x}\bigr)\tfrac{x^2}{\log^6 x}<\operatorname{gap}(x)$ | the same with $9.101$ |
| domain | every real $x>e^{3915}$ (strict) | the same ray |

`RamanujanGap.v2.strict_allowance_improvement` states only that $9.101<3914.7$, a comparison of
**certified allowances**. It says nothing about a ratio of true errors. The new result does **not**
lower the existing Boolean Ramanujan cutoff $e^{145}$ (that route uses other density and finite-RH
inputs). It does not claim to be best known or optimal.

### What remains assumed or trusted

- **Analytic premises.** These are explicit hypotheses, not reproved here:
  - old configuration: the PNT+ input `DudekPlattNumerics.v7.pi_asymmetric_pnt`;
  - new configuration: `QRHCH2.v5.psi_refined_bound`. In the canonical build,
    `ForwardRamanujan.forward` takes it as a hypothesis. A separate replay at Lean 4.34.1 supplies
    it from the actual OpenAI QRH proof plus 13 CH2 hypotheses.
- **Numerical trust.** Each budget certificate uses six finite `native_decide` facts, which the
  compiler checks rather than the kernel. This is *not* official three-axiom compliance.
- **Not verified at all.** The compiler, runtime and hardware are trusted. Agreement with GCC output
  bits is a diagnostic only.

---

## Depth 2: why the computation proves the claim

Each step below runs **definition → small example → hypotheses → conclusion → next consumer**.

### Step 1. Definition: the seventh-order error

The repaired criterion `DudekPlatt.v3.criterion` reduces Ramanujan's inequality to one condition.
The condition compares the seventh-order error
$\varepsilon(x)=\varepsilon_{\rm Upper}(M,x)-\varepsilon_{\rm Lower}(m,x_a,x)$ with $\log x$.
Here

$$
\varepsilon_{\rm Upper}(M,x)=72+2M+\tfrac{2M+132}{\log x}+\tfrac{4M+288}{\log^2x}+\tfrac{12M+576}{\log^3x}+\tfrac{48M}{\log^4x}+\tfrac{M^2}{\log^5x}.
$$

$\varepsilon_{\rm Lower}$ splits on the sign of $m$, and that split is the erratum the node
repairs. For $m<0$ the coefficient of $m$ is $(1+1/\log x_a)^6$, not $1$.

The numerical node states a **uniform budget** for this error:
`RamanujanNumerics.v2.epsilon_budget` says $\varepsilon(x)\le 9.101$ for every $x>e^{3915}$, with
$M=131$, $m=119$ and $x_a=e^{3914}$.

### Step 2. A small example: the actual instance, in exact arithmetic

Program B evaluates seven terms; they are listed in `ForwardRamanujan.terms`. With $Y=3915$
standing for the smallest $\log x$ on the ray, the new instance's terms are

$$
262,\;\tfrac{394}{3915}\approx0.10064,\;\tfrac{812}{3915^2}\approx5.3\cdot10^{-5},\;\ldots,\;\tfrac{131^2}{3915^5}\approx1.9\cdot10^{-14},\;0,
$$

where the last term is $\max(0,-m)(1+1/A)^6=0$ because $m=119>0$. Their sum minus the fixed offset
$134$ and minus $\max(0,m)=119$ is

$$
\operatorname{upper}(119,131,3914,3915)=9.10069158\ldots\le 9.101 .
$$

For the old instance $(m,M)=(-1194,1426)$ the same recipe gives $3914.59411\ldots\le 3914.7$.
These are the exact rational values of the expressions the program evaluates. The program computes
them in binary64, and Lean proves that the rounding cannot push the result past the stated bound.

### Step 3. Hypotheses: why one number covers the whole ray

`ForwardRamanujan.epsilon_majorant` needs only $M\ge0$, $Y>0$ and $Y\le\log x$. Every term of
$\varepsilon_{\rm Upper}$ has a nonnegative numerator over a power of $\log x$, so it only decreases
as $\log x$ grows. The lower term is at least $206+\max(0,m)-\max(0,-m)(1+1/A)^6$ once the positive
$1/\log^k x$ terms are dropped. Hence $\varepsilon(x)\le\operatorname{upper}(m,M,A,Y)$ for **every**
$x$ with $\log x\ge Y$. This is a monotonicity argument, not sampling on a grid.

### Step 4. The program and its certificate (runtime work vs offline work)

- **Offline (generator + Lean check).** Each term is divided by $4096=2^{12}$ and rounded **up** to
  a binary64 number; these are the seven literals in `c/updated.c`. Lean checks with exact rational
  arithmetic that $\text{term}_j/4096\le\text{literal}_j$ (`enclosure_check`) and that every
  literal is a valid normal binary64 input (`domain_check`).
- **Runtime (the C program).** `double s = sum(inputs,7); r = s*4096.0; r = r-134.0; r = r-119.0;`
  (`ramanujan_epsilon_bound`). The sum is the shared indexed loop `sum`.
- **The bridge theorem.** `ForwardRamanujan.source_linked_upper` (frozen in
  `Solutions/RamanujanNumerics.v1/ForwardRamanujan/Source.lean`) works for any program record. If
  the source text tokenizes to the modelled program (`source_check`) and the modelled RN64 execution
  returns `out` (`execution_check`), then

  $$
  \textstyle\sum_j \text{term}_j-134-119\;\le\;\text{out}+\underbrace{4096\Bigl(\tfrac{s}{1-\gamma_6}-s\Bigr)+10^{-10}}_{\text{forward error}} .
  $$

  The $\gamma_6$ factor bounds the error of a seven-term floating-point sum. It is proved once, for
  all inputs, in the summation stability theory reused from `Solutions/FKS2Numerics.v2`. The
  $10^{-10}$ term covers the three suffix roundings (`suffix_check`).
- **Final check.** $\text{out}+\text{forward error}\le 9.101$ (`budget_check`). The modelled output
  bits are `0x4022338dd9402a60`.

No field of the execution relation states the desired inequality. The inequality is derived from
the generic theorem.

### Step 5. Conclusion: from the budget to the prime-counting gap

`ForwardRamanujan.gap_from_budget` needs $A>0$, $A+1\le Y$, the two-sided $\pi$ input, $x>e^Y$ and
$\varepsilon(x)\le C$. Under these it gives

$$
\operatorname{gap}(x) > x^2\,\frac{\log x - C}{\log^7 x}.
$$

`loss_from_budget` rewrites this as $\operatorname{loss}(x)\le C/\log x$ when $C\ge0$. The
**domain shift $x\mapsto x/e$** is the reason for the hypothesis $A+1\le Y$. The lower bound for
$\pi$ is applied at $x/e$ and so needs $x/e>e^{A}$, while the upper bound is applied at $x$ and needs
$x>e^{A+1}$. With $A=3914$ and $Y=3915$, both are guaranteed by $x>e^{3915}$.

### Step 6. Next consumer

`RamanujanGap.v2.loss_bound`, `.gap_lower_bound` and `.paired` consume exactly two propositions:
the $\pi$ input and the numerical budget. Nothing downstream imports them yet. The same
`gap_from_budget` with $C<\log x$ also re-derives the Boolean inequality of `DudekPlatt.v2` on this
ray (`RamanujanGap.v1.ramanujan`).

---

## Depth 3: verification and replay details

| Role | Declaration | File |
|---|---|---|
| Public budget, old / new | `RamanujanNumerics.v1.epsilon_budget` / `.v2.epsilon_budget` | `IEANTN/Nodes/RamanujanNumerics/v{1,2}/Conclusions.lean` |
| Provider theorem | `RamanujanNumerics.v2.challenge_epsilon_budget` (uses `ForwardRamanujan.Updated.epsilon_bound`) | `Solutions/RamanujanNumerics.v2/Solution.lean`, `ForwardRamanujanUpdate/Updated.lean` |
| Executed source | `ramanujan_epsilon_bound` (old `c/baseline.c`, new `c/updated.c`) | `Solutions/RamanujanNumerics.v{1,2}/c/` |
| Source model and generic soundness | `ForwardRamanujan.Exec`, `source_linked_upper`, `sum_upper` | `Solutions/RamanujanNumerics.v1/ForwardRamanujan/Source.lean` (frozen) |
| Generic mathematics | `epsilon_majorant`, `gap_from_budget`, `loss_from_budget` | `Solutions/RamanujanNumerics.v1/ForwardRamanujan/Math.lean` (frozen) |
| Six finite native facts per instance | `source_check`, `enclosure_check`, `domain_check`, `execution_check`, `suffix_check`, `budget_check` | `Old.lean` / `Updated.lean` |
| Updated consumers | `RamanujanGap.v2.challenge_{loss_bound,gap_lower_bound,paired,strict_allowance_improvement}` | `Solutions/RamanujanNumerics.v2/ForwardRamanujanUpdate/Consumer.lean`; `Solutions/RamanujanGap.v2/Solution.lean` only imports it |
| Paired assembly | `ForwardRamanujan.forward (hpsi : QRHCH2.v5.psi_refined_bound) : RamanujanGap.v2.paired ∧ RamanujanGap.v2.strict_allowance_improvement` | `ForwardRamanujanUpdate/Assembly.lean` |
| Kernel alternative for one fact | `ForwardRamanujan.KernelSource.source_guard` (standard axioms only); `certified_upper` (5 native facts) | `ForwardRamanujanUpdate/KernelSource.lean` |

Snapshots:

- The old source, its certificate and its consumer were frozen at `aedfab4` (2026-11-04 00:11:48
  UTC). The SHA256 values are in the forward baseline freeze manifest.
- Old output bits: `0x40ae95302f2fc329`. New output bits: `0x4022338dd9402a60`.

Replay: see [REPRODUCING.md](REPRODUCING.md) §3. To read the exact axiom closure:

```bash
(cd Solutions/RamanujanNumerics.v2 && lake env lean /tmp/QRHForwardPreview.lean)
```

The file contents are given in REPRODUCING.md. The expected closure: `forward` has 12 native facts
plus the 3 standard axioms, and each budget certificate has 6. Agent B's independent replay of these
counts is recorded in the integration result and is not part of this page.

What the numbers do **not** say:

- They are not a ratio of actual errors.
- They do not lower the existing $e^{145}$ Boolean cutoff.
- They show no reduction in workload: both inputs meet the old target with one grouped input and
  four floating-point operations.
- They involve no blind selection, because the implementer already knew M1.
