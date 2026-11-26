# Prime-population transfer at widths 3 and 5

## Statement and hypotheses

Write $y_c(x)=x+c\sqrt{x}\log x$, $N_c(x)=\#\{p:x<p\le y_c(x)\}$ and $N_c^\circ(x)=\#\{p:x<p<y_c(x)\}$. These are **total**, not half, width coefficients. $\mathrm{Good}(a,c)$ means $c>0$ and, for some $\delta>0$, eventually $N_c(x)/\sqrt x\ge a+\delta$. The estimates are for sufficiently large **real** $x$; the threshold can depend on the parameters and the proof. No onset is specified by the new results.

Use ordinary RiemannHypothesis and retain the named analytic predicates CMSFunctionalInput.v1.population_reduction (Gaussian only), BRFourierInput.v1.norm_identity and BRFourierInput.v1.uniform_population_q1 (affine only). Put
$
q=20582561296/24680948495,\quad
G(a)=q(1+2a),\quad S(a)=(944247+1163388a)/10^6,\quad F(a)=9/8+(16/15)a.
$
For $a\ge0$, the supplied claims are Good at $G(a)+\epsilon$ for every $\epsilon>0$, and at $S(a)$ and $F(a)$ themselves.

**At width 3 the strongest inverted target directly furnished by these three lines is $t_3=685251/387796$ (sparse); at width 5 it is $t_5=465/128$ (flat). Both are attained as Good bounds**, with only RH and the two BR inputs. In particular for each $c=3,5$ there is $d_c>0$ with both counts at least $(t_c+d_c)\sqrt x$ eventually. Section “Using the witness caps” below gives strictly sharper explicit leading targets when using the underlying certified witness facts rather than just the three line statements.

| total width | inverse Gaussian (boundary) | inverse sparse | inverse flat |
|---:|---:|---:|---:|
| 3 | $53460284189/41165122592$ | **$685251/387796$** | $225/128$ |
| 5 | $102822181179/41165122592$ | $4055753/1163388$ | **$465/128$** |

To invert a line $b+ma$ solve $a=(c-b)/m$. Here all slopes are positive, all six inverses are positive, and each row is ordered by the displayed column order except that the sparse and flat entries are reversed at 3. At a Gaussian inverse the positive width epsilon can be chosen for any smaller nonnegative target, not at equality. At the affine maxima substitution gives exactly the stated Good bounds; no limit argument is needed.

## Endpoint argument

For $x>1$ and $c>0$, the primes at most $x$ form a subset of those at most $y_c(x)$. At nonnegative real $z$, a natural prime is at most $z$ iff it is at most $\lfloor z\rfloor$; the cardinality is $\pi_{\mathbb R}(z)$. Subtracting the nested cardinalities counts $(x,y_c(x)]$ without including a prime at $x$. Only a prime equal to $y_c(x)$ can be lost in passing to strict-open, and there is at most one. Thus from Good with margin $\delta$,
$
N_c^\circ(x)\ge (a+\delta)\sqrt x-1\ge(a+\delta/2)\sqrt x
$
once $x>1$ and $x\ge(2/\delta)^2$, in addition to the Good threshold. This also gives the integer lower bound $\lfloor a\sqrt x\rfloor+1$ eventually for $a\ge0$. No prime-index result is assumed or needed.

## Exact lower width envelope of the three supplied lines

Let $A=544470055511653/2490320656859788$, $B=542259/290164$ and $T=172404138261/356130660736$. These are the positive crossings $G=S$, $S=F$ and $G=F$, respectively, by equating intercept plus slope times $a$. The slopes decrease strictly in the order $G,S,F$, and $0<A<T<B$. For each pair its difference (first minus second in that order) is the positive slope difference times $a$ minus the crossing times that same slope difference. Hence on $[0,A]$, $G$ is at most both lines; on $[A,B]$, $S$ is at most both; on $[B,\infty)$, $F$ is at most both. This gives the exact piecewise envelope $E=\min(G,S,F)$:
$
E(a)=\begin{cases}
G(a)&0\le a<A,\
S(a)&A\le a<B,\
F(a)&B\le a.
\end{cases}
$
Values agree at the joins. The widths delivered directly by the three statements and monotonicity are **$(E(a),\infty)$** for $0\le a<A$ and **$[E(a),\infty)$** for $a\ge A$. Indeed for $x>1$ the upper endpoint is increasing in $c$, so widening preserves Good. The exact direct certificate is $G(a)<c$ or $S(a)\le c$ or $F(a)\le c$. At $A$ the sparse line attains the envelope and at $B$ both affine lines attain it. For $0<a<A$ at width $E(a)$ itself one may use Gaussian for any target $0\le b<a$ with $\epsilon=G(a)-G(b)>0$; the same open-count conversion applies. This implies a normalized lower limit at least $a$, not a positive uniform margin over $a$. At $a=0$ this argument cannot establish a positive margin at $c=q$.

This is an envelope of the certificates, not the infimum of all valid widths for the primes. In particular, one cannot promote a pointwise family of strict margins to a uniform margin as parameters tend to a join or endpoint. As a check just on what the line inequalities encode, consider a hypothetical monotone count profile, not a claim about primes: set $M(c)=\max(0,G^{-1}(c),S^{-1}(c)+\eta,F^{-1}(c)+\eta)$ with $\eta>0$, and counts $\lfloor M(c)\sqrt x\rfloor$ for $x>1$. It satisfies the three line certificates, since the limit is $M(c)$, and it places the limit at a selected Gaussian boundary $a<A$ by taking $\eta$ smaller than both affine inverse deficits there. At either 3 or 5 the limit is just $t_c+\eta$, with $\eta$ arbitrarily small. Thus no larger explicit target at those widths follows just from the pointwise line assertions and width monotonicity.

## Exact comparison to the preserved octic baseline

The separate RH+Green+Nicolas+BPT result in the packet counts **strict-open** primes for $x\ge\exp(24)$ and $103/100\le c\le16$ with strict lower bound
$
[O(c)+(21/5)/\log x]\sqrt x,\qquad O(c)=(8/9)c-18203/20000.
$
At widths 3 and 5, within that domain, the exact leading comparisons are:
 
| $c$ | original leading $O(c)$ | new line target minus $O(c)$ | corresponding old leading width minus $c$ at target $t_c$ |
|---:|---:|---:|---:|
| 3 | $105391/60000$ | $61212941/5816940000$ | $183638823/15511840000$ |
| 5 | $636173/180000$ | $70933/720000$ | $70933/640000$ |

The inverse $W_O(a)=(9/8)(a+18203/20000)$ is in the original width range iff $973/180000\le a\le2396173/180000$, by solving the two linear inequalities. Both joins are in this range. On it the exact leading width savings $W_O(a)-E(a)$ are:
$
\begin{cases}
150039188346073/789790351840000-(107192444281/197447587960)a & a<A,\
318687/4000000-(9597/250000)a & A\le a<B,\
-16173/160000+(7/120)a & a\ge B.
\end{cases}
$
These follow by subtracting intercepts and slopes. Positivity: for $a\le2$, $W_O(a)-S(a)\ge W_O(2)-S(2)>0$; for $a\ge2$, $W_O(a)-F(a)\ge W_O(2)-F(2)>0$ (both comparisons at 2 are rational). Since $E$ is no larger than either line, the savings are positive. Where Gaussian is active the savings relative to $E$ are supremal: choose any $0<\epsilon<W_O(a)-E(a)$ to get a certified strictly smaller width, not the unperturbed Gaussian width.

Do not compare the new eventual bounds to the full old finite-$x$ RHS without its positive correction. For example at either input width the leading improvement $\Delta=t_c-O(c)>0$ exceeds the correction once $\log x>(21/5)/\Delta$, but one must **also** reach the unspecified new threshold. The old theorem itself gives strict count greater than $a\sqrt x$ at $W_O(a)$ throughout its domain and onset, without providing a positive *limiting* margin there just from the correction. In particular the baseline leading-count-1 width $343827/160000=2.14891875$ with $x\ge\exp(24)$ is preserved. No explicit onset is inherited and no comparison outside the original width range or to an overall literature optimum is made.

## Using the witness caps (separate refinement)

The frozen witness propositions supply $U\ge\|F_{\rm test}\|_1$, the exact denominator $D=F_{\rm test}(0)-4J$, and attained peak $M>0$. For sparse and flat, respectively:
 
| witness | $D$ | $U$ | $M$ |
|---|---|---|---|
| sparse | $1-4\cdot119725872611533800/(8\cdot10^{18})$ | $887721072633027910/10^{18}$ | $546871713113309800/10^{18}$ |
| flat | $15\cdot533333333333333333/(8\cdot10^{18})$ | $1120475208606944546/10^{18}$ | $533333333333333333/10^{18}$ |

The general BR estimate for the padded affine pair yields eventually a normalized lower bound $(cD-\|F_{\rm test}\|_1)/(2M)-C\,[\log\log x/\log x+2\log x/\sqrt x]$ for some fixed $C\ge0$ (per width and witness). Thus if $a<L(c)=(cD-U)/(2M)$, the error is eventually at most $(L(c)-a)/2$, giving Good. Using the better witness at each width gives:
 
| width | certified limiting threshold $L$ (all $a<L$ are Good) | $L-O(c)$ |
|---:|---:|---:|
| 3 (sparse) | $193269011844967139/109374342622661960$ | $1726734183826542841/164061513933992940000$ |
| 5 (flat) | $31036198331144443607/8533333333333333328$ | $9864964558708324124141/95999999999999999940000$ |

Both exceed the corresponding line target. For either endpoint convention, every real coefficient strictly below $L$ is an eventual lower bound with a positive margin, so the normalized lower limit is at least $L$. These are the best thresholds of these two substitutions, not claimed to be attained Good bounds at $L$ or global optima. Approaching $L$ increases the required precision on the remainder. The displayed $E$ is still exactly the envelope of the **three specified curves**, not a claim to include this additional use of their witnesses.

## Evidence and scope

* Written arguments above; exact arithmetic and source-byte checks in `check.py`. `Transfer.lean` proves the envelope, the exact direct certificate, attainment/epsilon results, the strict-open membership and count transfer, the fixed widths and comparison arithmetic. Both named affine proof routes are used; the root theorems ending in `_actual` compose the inherited source-first route with the new mathematics. `WitnessRefinement.lean` checks the separate stronger targets starting from the certified norm bounds and the general analytic consumer.
* CMS frozen primary: `/corpus/literature/CMS1708.04122v2.pdf`, admissible-class definition (1.3), (1.11)–(1.12), Theorem 3 (1.13), §5.2; corresponding text lines 260–275 for the bound. Exact Lean predicate via `IEANTN/Nodes/CMSFunctionalInput/v1/Conclusions.lean` and `IEANTN/Vocabulary/CMSFunctional.lean:73–80`. Kernel Gaussian root `RH080EstimatePack.lean:9` uses `Scaled40ActualConsumers.lean:47`; it is not a source-first numerical route.
* BR frozen primary: `/corpus/literature/Blanquer_Robles_2026.pdf`, §2.1 Lemma 5, (4) for the arbitrary rational support-five affine norm identity; §3 Proposition 6 and its proof, including the conductor-one case and the “moduli 1 and 2” paragraph, for the $q=1$ restriction. Exact Lean predicates via `IEANTN/Nodes/BRFourierInput/v1/Conclusions.lean`, `BRSourceInterfaces.lean:17–21`, and `ExplicitBRPopulationConsumer.lean:21–94`. The new constants are not literal statements of those papers. These propositions remain hypotheses, not Lean analytic derivations from RH.
* All Lean source locators for inherited work are relative to `/source_pv/source`. Matched kernel root `RH080EstimatePack.lean` uses `PopulationMatchedControl.lean`. The D source-first roots are `PopulationActualConsumers.lean` (`source_first_sparse_curve`, `source_first_flat_curve`) via `AffineProgramsSolution.lean:29–50`. The source pairs `PopulationSource.lean` / `FlatPopulationSource.lean` check lexer, AST token correspondence and preprocessing for embedded strings matching `/source_pv/population_norm.c` and `/source_pv/flat_population_norm.c`. The respective `*Execution`, `*Main`, `*SourceFinal` give checked scalar execution, modeled printf output and its consumption in a certified norm bound, not a mere matching sample. The BR norm identity then transfers to the inverse-transform norm. The port is fixed-input scalar C in the checked subset under its modeled types, checked 64-bit arithmetic and host print harness (`ScalarHost.lean`). It is not a verified portable C/C++/CUDA toolchain, machine-code, runtime, OS or hardware execution. Neither the Gaussian chain nor the separate large FFT migration is covered by this source-first claim.
* `failed.md` records unsuccessful attempts and remaining limitations. The original octic numerical result is taken as a packet baseline under its separate assumptions, not reproved here.

### Replay

From `/work/submission`, with the assigned bounded wrapper and mounts:

```sh
/usr/bin/python3.10 -c 'from pathlib import Path; Path("/work/objects").mkdir(exist_ok=True)'
/bin/lean -o /work/objects/Transfer.olean Transfer.lean
/bin/lean WitnessRefinement.lean
/usr/bin/python3.10 check.py
```

Read the exit status and the printed axiom audits. The successful local replays reported only the standard `propext`, `Classical.choice`, and `Quot.sound` dependencies for the audited results; the named analytic inputs and RH are theorem parameters. The Python arithmetic is a cross-check, not the source of a numerical hypothesis.
