# FKS2 Table 4 pair: what is proved, why the program proves it, how to check it

This page is for a reader trained in mathematics who has not seen the C or Lean source. It covers
the providers `FKS2Numerics.v6` (old, frozen) and `FKS2Numerics.v7` (QRH), their premises
`FKS2.v8` (published Table 3 rows, frozen) and `FKS2.v6.table4_anchor_300`, and the consumer
`FKS2.v9`. The statements are in the nodes' `Conclusions.lean`. This page explains them and does
not replace them.

**Status in one line.** For every real $x\ge e^{330}$, the program-checked allowance for the
normalized error of $\pi(x)$ against $\operatorname{Li}(x)$ is $1.69\cdot10^{-12}$ (old inputs,
reconstructed) and $5\cdot10^{-16}$ (QRH inputs). The old program was reconstructed after the
fact, and the comparison is between certified allowances. Neither result is a best-known envelope:
the existing Phase 2 density route is stronger on this ray under additional inputs. There is no
official receipt. Each program depends on 8 finite `native_decide` facts.

---

## Depth 1: the claim

### The quantity

$$
E_\pi(x)=\frac{|\pi(x)-\operatorname{Li}(x)|}{x/\log x},\qquad \operatorname{Li}(x)=\int_2^x\frac{dt}{\log t}.
$$

These are `IEANTN.Eπ` and `IEANTN.Li`. `HasNumericalBound Eπ c x₀` means $E_\pi(x)\le c$ for every
$x\ge x_0$. `FKS2.v9` states the same bounds without the normalization:
$|\pi(x)-\operatorname{Li}(x)|\le c\,x/\log x$.

### Hypotheses

| Configuration | $\theta$ input on $[e^{300},\infty)$ | Anchor at $e^{300}$ | Remaining premises |
|---|---|---|---|
| Old, `FKS2Numerics.v6.old_pi` | FKS2 Table 3 rows 300, 310, 320, 330 (`FKS2.v8.table3_theta_*`): $E_\theta\le 1.6930,\,1.6882,\,1.6837,\,1.6795\ (\times10^{-12})$ on the whole tail from each row | `FKS2.v6.table4_anchor_300`: $E_\pi(e^{300})\le1.6997\cdot10^{-12}$ | Four published rows plus the anchor |
| QRH, `FKS2Numerics.v7.qrh_pi` | `QRHCH2.v5.psi_refined_bound`, giving $E_\theta(t)\le Q(b)=\tfrac{b^2}{283}e^{-b/8}$ for $t\ge e^{b}$ | the same anchor | The QRH-derived $\psi$ bound plus the anchor. In the canonical build QRH itself enters through `FKS2Pair.assembled`'s explicit argument. The separate replay at Lean 4.34.1 supplies the actual OpenAI theorem and leaves 13 CH2 hypotheses |

### Conclusions

| | Allowance on $x\ge e^{330}$ |
|---|---|
| `FKS2.v9.old_absolute_pi` | $|\pi(x)-\operatorname{Li}(x)|\le 1.69\cdot10^{-12}\,x/\log x$ |
| `FKS2.v9.qrh_absolute_pi` | $|\pi(x)-\operatorname{Li}(x)|\le 5\cdot10^{-16}\,x/\log x$ |
| `FKS2.v9.exact_allowance_ratios` | $1.69\cdot10^{-12}/5\cdot10^{-16}=3380$ and $1.6855\cdot10^{-12}/5\cdot10^{-16}=3371$ (allowances, not true errors) |

$1.6855\cdot10^{-12}$ is the **published** FKS2 Table 4 value. $1.69\cdot10^{-12}$ is **our
reconstruction** of the old program, built with the same 30 cells. They are different numbers, and
neither is the true error.

### What remains assumed or trusted

- **Analytic premises.** The published Table 3 rows and the anchor are literature inputs. The QRH
  route depends on the CH2 chain (13 named hypotheses) and on the QRH theorem.
- **Numerical trust.** Each program depends on 8 finite native facts.
- **Not verified at all.** The compiler, runtime and hardware are trusted.
- **Fixed geometry.** The cells run from $\log x = 300$ to $330$, so there are 30 of them.
  Arbitrary partitions are **not** supported.

---

## Depth 2: why the computation proves the claim

### Step 1. Definition: the profile and the safe bound

A **profile** is a list of 31 nonnegative whole-tail allowances $U_0,\dots,U_{30}$ such that
$E_\theta(t)\le U_j$ for every $t\ge e^{300+j}$. This is `FKS2Pair.ValidProfile`. From a profile the
proof builds

$$
B_{\rm safe}[U]=\underbrace{\tfrac{330}{300}e^{-30}\bigl(1.6997\cdot10^{-12}+U_0\bigr)}_{\text{anchor}}
+\sum_{j=0}^{29}\underbrace{\frac{330\,U_j}{b_j^2}(e-1)\,e^{b_j-330}}_{\text{cell }j,\ b_j=300+j}
+U_{30}+\frac{U_{30}}{328}.
$$

(`FKS2Pair.Bsafe`, `cellU`, `anchor`).

### Step 2. A small example (pedagogical only)

> *This toy example is not the certified instance.* Suppose, for illustration, that every
> $U_j=10^{-12}$. The last cell ($b=329$) contributes about
> $\frac{330\cdot10^{-12}}{329^2}(e-1)e^{-1}\approx1.9\cdot10^{-15}$, and each cell before it is $e$
> times smaller. The thirty cells together therefore contribute about $3.1\cdot10^{-15}$, and the
> anchor contributes about $3\cdot10^{-25}$. The total is dominated by the point term $U_{30}$
> plus $U_{30}/328$ ($1.00305\cdot10^{-12}$), giving about $1.0061\cdot10^{-12}$.

The real old profile is FKS2's Table 3 rows, applied with no interpolation: row 300 for
$j<10$, row 310 for $j<20$, row 320 for $j<30$, row 330 at $j=30$. Its exact value is
$B_{\rm safe}\approx1.68977\cdot10^{-12}$:

- point and tail terms: $1.68462\cdot10^{-12}$;
- cells: $5.15\cdot10^{-15}$;
- anchor: $3.5\cdot10^{-25}$.

After upward rounding the program certifies $1.69\cdot10^{-12}$. The QRH profile is $U_j=Q(300+j)$.
Its exact value is about $4.7155\cdot10^{-16}$, and the program certifies that it is below
$5\cdot10^{-16}$. These exact values were evaluated with mpmath at 30 digits as a cross-check; the
certificates themselves are in Lean.

### Step 3. Hypotheses: why one number covers the whole ray

`FKS2Pair.whole_ray_transport` needs a valid profile and the anchor. It writes
$\pi(x)-\operatorname{Li}(x)$ by partial summation from $e^{300}$ and then splits it into four
pieces:

- an anchor term at $e^{300}$;
- the integral of $(\theta(t)-t)/(t\log^2t)$ over $[e^{300},e^{330}]$, bounded cell by cell by
  $U_j\int dt/\log^2t$;
- the point term $(\theta(x)-x)/\log x$;
- the tail integral over $[e^{330},x]$, bounded by $U_{30}/328$.

Multiplying by $\log x/x$, which decreases for $x\ge e$, makes every piece at most its value at the
left endpoint. The conclusion is $E_\pi(x)\le B_{\rm safe}[U]$ for **every** $x\ge e^{330}$. Like
the Ramanujan budget, this is a monotonicity theorem and not grid sampling.

### Step 4. The program and its certificate (runtime work vs offline work)

- **Offline (generator + Lean check).** Each cell value contains $e^{b-330}$. Lean encloses it
  rigorously with a Taylor polynomial plus a remainder bound (`FKS2Scalar.expCheck_sound`, an
  exact rational computation; it is not an opaque `exp`). The enclosed cell value, scaled by $2^{48}$
  (old) or $2^{58}$ (QRH), is rounded **up** to binary64. These are the 30 literals in the C file.
  The anchor, point and tail allowances are likewise rounded up to binary64.
- **Runtime (the C program).** The program sums the 30 literals with the shared indexed loop, scales
  the sum back exactly, and adds the anchor, point and tail literals. It calls no `exp`, `log` or
  `Li`.
- **The bridge theorem.** The same generic summation stability theorem as in the Ramanujan pilot
  gives $B_{\rm safe}[U]\le\text{out}+\text{forward error}$ (`FKS2Pair.Updated.verified_qrh_transport`).
  The budget check then gives `FKS2Pair.Updated.certified_allowance`:
  $B_{\rm safe}[Q]<5\cdot10^{-16}$.

### Step 5. Conclusion

`FKS2Pair.Updated.numerical_pi` combines the transport with the certified allowance and yields
`FKS2Numerics.v7.qrh_pi`. `FKS2.v9.challenge_qrh_absolute_pi` then removes the normalization.

### Step 6. Next consumer, and one design difference from the Ramanujan pilot

The Table 4 provider node publishes the **whole-ray $\pi$ bound**, which already includes the
analytic transport. Its purely numerical obligation, $B_{\rm safe}[Q]<5\cdot10^{-16}$, is a Lean
theorem inside the solution and not a node of its own. The Ramanujan pilot is built the other way:
it publishes the numerical budget as its own node, and a separate node consumes it. Both are valid.
The Ramanujan layout lets a second consumer reuse the budget without importing the transport.

---

## Depth 3: verification and replay details

| Role | Declaration | File |
|---|---|---|
| Public provider, old / QRH | `FKS2Numerics.v6.old_pi` / `FKS2Numerics.v7.qrh_pi` | `IEANTN/Nodes/FKS2Numerics/v{6,7}/Conclusions.lean` |
| Generic transport | `FKS2Pair.ValidProfile`, `Bsafe`, `whole_ray_transport` | `Solutions/FKS2Numerics.v6/FKS2Pair/GenericMath.lean` (frozen) |
| Generic source | `ExecTransportAt` | `Solutions/FKS2Numerics.v6/FKS2Pair/GenericSource.lean` (frozen) |
| Old program | `FKS2Pair.Old.*` and `c/fks2_table4_transport_old.c`, output bits `0x3d7dba0e6c578b0f` | `Solutions/FKS2Numerics.v6/` (frozen) |
| QRH program | `FKS2Table4.*`, source `c/fks2_table4_transport.c` | `Solutions/FKS2Numerics.v5/` |
| QRH adapter and provider | `FKS2Pair.qProfile_valid`, `qBsafe_eq`, `FKS2Pair.Updated.{verified_qrh_transport, certified_allowance, numerical_pi}` | `Solutions/FKS2Numerics.v6/FKS2Pair/QRHGeometry.lean`, `Solutions/FKS2Numerics.v7/FKS2PairQRH.lean` |
| Consumers | `FKS2.v9.challenge_*` | `Solutions/FKS2Numerics.v7/FKS2PairConsumers.lean` |
| Assembly | `FKS2Pair.assembled` (19 mathematical arguments: 4 Table 3 rows, 13 CH2, QRH, anchor) | `Solutions/FKS2Numerics.v7/FKS2PairReplay.lean` |

Snapshots:

- The old program and its proof were frozen at `fdfc454`.
- The shared transport and the paired consumers were added at `154b1d0`.

Replay: see [REPRODUCING.md](REPRODUCING.md) §2.
