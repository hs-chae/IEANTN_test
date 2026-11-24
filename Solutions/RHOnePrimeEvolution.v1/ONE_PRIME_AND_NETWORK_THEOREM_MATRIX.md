# One-prime and network theorem matrix

Universe: exactly all 24 conclusion definitions in RHOnePrimeEvolution.v1 (12), PrimePowerPopulation.v1 (6), Goldbach.v3 (3), and PrimeQuantile.v4 (3). This is not a global IEANTN audit. Each identity is keyed by file, declaration, and physical LF line. Exact Lean definitions and proof headers follow the table.

Notation: f(x)=√x log x; N(a,b) counts natural primes with BOTH real endpoints excluded. Prime indices start at zero. U(x)=x+2+c(log(x+1))f(x+1), where c(L)=[1−2(log(.399L)−1.17)/L]/1.14068+1/(10000L).

Numerical status for the selected final proof chains: D, Lean kernel checking; allowed standard axioms propext, Classical.choice, Quot.sound, no native execution axiom. Final fresh build: PASS_FRESH_TRANSITIVE_COMPILATION. Independent final-object audit: see evidence/integration-review/fresh-v1/RESULT.json. Source-first PV: NO for every row. External numerical searches are E and supply no antecedent to any row. No row is a Mathlib-RH-only theorem unless its displayed assumptions are elementary-only.

Exact source premises: CMS v2 §6.3 equation (6.16), including the disclosed entire/removable extension and Fourier/L1 identification ([primary](https://arxiv.org/pdf/1708.04122v2#page=26)); historical Nicely 2019 consecutive gaps below2^64, not a new verification; and the unchanged Green/Nicolas/BPT predicates from the frozen3539bbba package. The four consumer versions inherit that package through PrimeInterval.v4. Source URLs/version/hash manifest is sources/DOWNLOADS.json; complete source audit notes are in integration_review/ and powers/*REVIEW.json.

| Actual declaration identity | Exact quantified target (see source definition below) | Antecedents consumed by proof | Baseline / strict comparison | Numerical / PV / receipt | Confidence limitation |
|---|---|---|---|---|---|
| [RHOnePrimeEvolution.v1.kernel_ratio_lower](../../IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean#L21) · IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:21 | Actual sine-integral quotient ≥1.14068. | No external mathematical premise. | Improves proved 1.1405 numerical checkpoint. | D / no source-first PV / fresh297 + independent24root audit | The Fourier/norm identification is a separate B input. |
| [RHOnePrimeEvolution.v1.late_open_08768](../../IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean#L23) · IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:23 | All real x≥exp44: prime in (x,x+0.8768f(x)). | CMSCosineInput.v1.obstruction + RH.v1.hypothesis + kernel_ratio_lower. | Strictly shorter than CMS 0.88 on this ray. | D / no source-first PV / fresh297 + independent24root audit | New CMS source premise; not a record against 2026 0.85125. |
| [RHOnePrimeEvolution.v1.uniform_open_08768](../../IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean#L27) · IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:27 | All real x≥exp24: prime in (x,x+0.8768f(x)). | late_open_08768 + PrimeGapTable.v1.gaps. | Extends the proved late ray, improves 0.88 width. | D / no source-first PV / fresh297 + independent24root audit | Historical gap-table computation not newly verified. |
| [RHOnePrimeEvolution.v1.finite_slab_open_08301](../../IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean#L30) · IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:30 | exp44≤x≤exp59: prime in (x,x+0.8301f(x)). | CMSCosineInput.v1.obstruction + RH.v1.hypothesis. | Preserved first checkpoint, superseded by 0.8185. | D / no source-first PV / fresh297 + independent24root audit | Bounded, not an asymptotic gap coefficient. |
| [RHOnePrimeEvolution.v1.finite_absolute_1551](../../IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean#L33) · IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:33 | exp24≤x<exp44: prime in (x,x+1551). | PrimeGapTable.v1.gaps. | Absolute-width finite bridge. | D / no source-first PV / fresh297 + independent24root audit | Depends on reported Nicely computation; no RH required. |
| [RHOnePrimeEvolution.v1.consecutive_gap_08768](../../IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean#L36) · IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:36 | Consecutive natural primes p<q, p≥exp24: q−p<0.8768f(p). | uniform_open_08768. | New strict consecutive-gap consumer of the hybrid. | D / no source-first PV / fresh297 + independent24root audit | The input theorem carries its original premises. |
| [RHOnePrimeEvolution.v1.continuous_late](../../IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean#L42) · IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:42 | All real x≥exp44: prime in (x,U(x)), U=x+2+c(log(x+1))f(x+1). | CMSCosineInput.v1.obstruction + RH.v1.hypothesis. | Whole-variable endpoint, not just one constant. | D / no source-first PV / fresh297 + independent24root audit | U definition and entire endpoint shift retained. |
| [RHOnePrimeEvolution.v1.continuous_improves_uniform](../../IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean#L45) · IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:45 | All real x≥exp44: U(x)<x+0.8768f(x). | No external mathematical premise. | Strict whole-ray endpoint comparison. | D / no source-first PV / fresh297 + independent24root audit | No superiority over all current literature frontiers claimed. |
| [RHOnePrimeEvolution.v1.continuous_uniform](../../IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean#L48) · IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:48 | All real x≥exp24: prime in (x,if x<exp44 then x+1551 else U(x)). | continuous_late + PrimeGapTable.v1.gaps. | Short finite window plus variable late frontier. | D / no source-first PV / fresh297 + independent24root audit | Historical finite computation stays an explicit separate input. |
| [RHOnePrimeEvolution.v1.bounded_open_08357](../../IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean#L52) · IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:52 | All real exp24≤x≤exp110: prime in (x,x+0.8357f(x)). | CMSCosineInput.v1.obstruction + RH.v1.hypothesis + PrimeGapTable.v1.gaps. | Numerically below 0.8358 on a bounded domain. | D / no source-first PV / fresh297 + independent24root audit | Does not beat an asymptotic theorem as a quantified proposition. |
| [RHOnePrimeEvolution.v1.bounded_open_08512](../../IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean#L56) · IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:56 | All real exp24≤x≤exp225: prime in (x,x+0.8512f(x)). | CMSCosineInput.v1.obstruction + RH.v1.hypothesis + PrimeGapTable.v1.gaps. | Below printed fixed 2026 0.85125 width on this domain. | D / no source-first PV / fresh297 + independent24root audit | Not a comparison with full retunings of the 2026 inequalities. |
| [RHOnePrimeEvolution.v1.bounded_open_08185](../../IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean#L59) · IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:59 | All real exp24≤x≤exp59: prime in (x,x+0.8185f(x)). | CMSCosineInput.v1.obstruction + RH.v1.hypothesis + PrimeGapTable.v1.gaps. | Improves earlier 0.8301/0.819 checkpoints. | D / no source-first PV / fresh297 + independent24root audit | Credible written 2026 retuning gives a stronger 0.8111 competitor. |
| [PrimePowerPopulation.v1.cube_population_all_real](../../IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean#L12) · IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean:12 | All real n≥exp8: N(n³,(n+1)³)>(5.08985+1.4/logn)n√n. | PrimeInterval.v4.optimized_strict_family. | Replaces one-prime cube existence by an explicit count. | D / no source-first PV / fresh297 + independent24root audit | Same inherited RH+Green+Nicolas+BPT package; no new kernel. |
| [PrimePowerPopulation.v1.cube_density_all_real](../../IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean#L18) · IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean:18 | All real n≥exp8: N(n³,(n+1)³)>0.70n²/logn. | PrimeInterval.v4.optimized_strict_family. | New disjoint-cell square/log scale; improves 0.648 branch. | D / no source-first PV / fresh297 + independent24root audit | No global prime-between-cubes record; different PNT inputs may be stronger. |
| [PrimePowerPopulation.v1.cube_density_natural](../../IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean#L23) · IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean:23 | All natural n≥2981: N(n³,(n+1)³)>0.70n²/logn. | PrimeInterval.v4.optimized_strict_family. | Concrete natural onset with actual exp8<2981 proof. | D / no source-first PV / fresh297 + independent24root audit | No all-consecutive-squares inference. |
| [PrimePowerPopulation.v1.higher_power_population](../../IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean#L29) · IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean:29 | All real n≥exp8 and natural exponent r≥3: N(n^r,(n+1)^r)>(5.08985+4.2/(rlogn))√(n^r). | PrimeInterval.v4.optimized_strict_family. | Actual counts for every integer exponent ≥3. | D / no source-first PV / fresh297 + independent24root audit | Not a theorem for arbitrary real r>2. |
| [PrimePowerPopulation.v1.cube_frontier](../../IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean#L35) · IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean:35 | All real n≥exp8: count exceeds max(one-window count,0.70n²/logn). | PrimeInterval.v4.optimized_strict_family. | Retains small-n branch and stronger large-n density. | D / no source-first PV / fresh297 + independent24root audit | No branch deleted; onset unchanged. |
| [PrimePowerPopulation.v1.density_improves_648](../../IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean#L42) · IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean:42 | All real n≥exp8: 0.648n²/logn<0.70n²/logn. | No external mathematical premise. | Strict same-domain density comparison. | D / no source-first PV / fresh297 + independent24root audit | This scalar comparison alone is not a prime theorem. |
| [Goldbach.v3.sorted_count_extended](../../IEANTN/Nodes/Goldbach/v3/Conclusions.lean#L16) · IEANTN/Nodes/Goldbach/v3/Conclusions.lean:16 | All natural H,n with finite binary Goldbach through H, Odd n,3H≤2n, u=n−H≥exp24,C*u^0.5*logu≤H−4: sortedTriples(n)>(1/2+2.1/logu)√u, C=2.14891875. | PrimeInterval.v4.optimized_strict_family. | New range 3H≤2n with sorting-fiber bound two instead of injectivity. | D / no source-first PV / fresh297 + independent24root audit | Finite binary Goldbach and width/onset explicit; equality n=2H adds no odd cases. |
| [Goldbach.v3.sorted_count_full_finite_range](../../IEANTN/Nodes/Goldbach/v3/Conclusions.lean#L24) · IEANTN/Nodes/Goldbach/v3/Conclusions.lean:24 | All natural H,n with finite binary Goldbach through H, Odd n,u=n−H≥exp24,C√u logu≤H−4: sortedTriples(n)>(1/3+1.4/logu)√u. | PrimeInterval.v4.optimized_strict_family. | Removes n/H ratio requirement by sorting-fiber bound three. | D / no source-first PV / fresh297 + independent24root audit | Not a proof of binary Goldbach or an RH-only ternary computation. |
| [Goldbach.v3.sorted_count_750m_band](../../IEANTN/Nodes/Goldbach/v3/Conclusions.lean#L34) · IEANTN/Nodes/Goldbach/v3/Conclusions.lean:34 | Finite binary Goldbach through 4e18 implies >750000000 sorted triples for every odd natural 6e18≤n≤8e18. | PrimeInterval.v4.optimized_strict_family. | Nonempty new band excluded by old n>8e18 injective route. | D / no source-first PV / fresh297 + independent24root audit | No new source-first proof of the finite binary input. |
| [PrimeQuantile.v4.strict_generic_block](../../IEANTN/Nodes/PrimeQuantile/v4/Conclusions.lean#L14) · IEANTN/Nodes/PrimeQuantile/v4/Conclusions.lean:14 | Every C∈[1.03,16], real x≥exp24 and natural m≤(8C/9−.91015+4.2/logx)√x: x<p_{π(x)+m}<x+Cf(x), zero-based primes. | PrimeInterval.v4.optimized_strict_family. | Full exact count margin and strict upper endpoint. | D / no source-first PV / fresh297 + independent24root audit | Zero-based indexing, floor of real x, and m≤margin retained. |
| [PrimeQuantile.v4.strict_special_block](../../IEANTN/Nodes/PrimeQuantile/v4/Conclusions.lean#L23) · IEANTN/Nodes/PrimeQuantile/v4/Conclusions.lean:23 | Real x≥exp24, natural m≤(180173/180000+5.8/logx)√x: x<p_{π(x)+m}<x+2.15f(x). | PrimeInterval.v4.optimized_strict_215. | Preserves stronger specialized residual and opens upper endpoint. | D / no source-first PV / fresh297 + independent24root audit | Specialized count not replaced by weaker generic 4.2 term. |
| [PrimeQuantile.v4.shifted_sqrt_block](../../IEANTN/Nodes/PrimeQuantile/v4/Conclusions.lean#L32) · IEANTN/Nodes/PrimeQuantile/v4/Conclusions.lean:32 | Real x≥exp24, natural m≤√x: x<p_{π(x)+m}<x+2.14891875f(x)−4.725√x. | PrimeInterval.v4.optimized_strict_family. | Strictly shorter by exactly4.725√x at same index targets. | D / no source-first PV / fresh297 + independent24root audit | Fixed-x width saving, not an optimized finite H at fixed n. |

## Exact declarations and actual proof headers

These are extracted from the pinned current sources; the proof headers expose the typed canonical input edges. Analytic input provenance is not erased by the short canonical names.

### RHOnePrimeEvolution.v1.kernel_ratio_lower

Conclusion: `IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:21`, SHA-256 `eb72cdde5f6b8dacdfc613a35f1e03b63b14a747274df83b97f57fbe0a1a6d89`. Proof: `Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean:20`, SHA-256 `72d85077cb5ff686a9061198c97a787b374032d955e405d6f678d20fa67635e2`.

```lean
def kernel_ratio_lower : Prop := (28517 / 25000 : ℝ) ≤ cmsJ
/-- Analytic ray with both endpoints open; no finite-gap-table input. -/
def late_open_08768 : Prop := ∀ x : ℝ, exp 44 ≤ x →
  hasPrimeOpen x (x + (548 / 625) * sqrt x * log x)
/-- Uniform ray after the finite/analytic split, retaining the finite computation
as a separate input. This is not its new formal verification. -/
def uniform_open_08768 : Prop := ∀ x : ℝ, exp 24 ≤ x →
  hasPrimeOpen x (x + (548 / 625) * sqrt x * log x)
/-- Bounded explicit improvement, not asymptotic domination of0.8358. -/
def finite_slab_open_08301 : Prop := ∀ x : ℝ, exp 44 ≤ x → x ≤ exp 59 →
  hasPrimeOpen x (x + (8301 / 10000) * sqrt x * log x)
/-- Absolute finite-range window, requiring no RH hypothesis. -/
def finite_absolute_1551 : Prop := ∀ x : ℝ, exp 24 ≤ x → x < exp 44 →
  hasPrimeOpen x (x + 1551)
/-- Consecutive-prime consumer of the uniform open interval. -/
def consecutive_gap_08768 : Prop := ∀ p q : ℕ,
  p.Prime → q.Prime → p < q → exp 24 ≤ (p : ℝ) →
  (∀ r : ℕ, p < r → r < q → ¬ r.Prime) →
    (q : ℝ) - p < (548 / 625) * sqrt (p : ℝ) * log (p : ℝ)

theorem challenge_kernel_ratio_lower : kernel_ratio_lower :=
```

### RHOnePrimeEvolution.v1.late_open_08768

Conclusion: `IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:23`, SHA-256 `eb72cdde5f6b8dacdfc613a35f1e03b63b14a747274df83b97f57fbe0a1a6d89`. Proof: `Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean:47`, SHA-256 `72d85077cb5ff686a9061198c97a787b374032d955e405d6f678d20fa67635e2`.

```lean
def late_open_08768 : Prop := ∀ x : ℝ, exp 44 ≤ x →
  hasPrimeOpen x (x + (548 / 625) * sqrt x * log x)
/-- Uniform ray after the finite/analytic split, retaining the finite computation
as a separate input. This is not its new formal verification. -/
def uniform_open_08768 : Prop := ∀ x : ℝ, exp 24 ≤ x →
  hasPrimeOpen x (x + (548 / 625) * sqrt x * log x)
/-- Bounded explicit improvement, not asymptotic domination of0.8358. -/
def finite_slab_open_08301 : Prop := ∀ x : ℝ, exp 44 ≤ x → x ≤ exp 59 →
  hasPrimeOpen x (x + (8301 / 10000) * sqrt x * log x)
/-- Absolute finite-range window, requiring no RH hypothesis. -/
def finite_absolute_1551 : Prop := ∀ x : ℝ, exp 24 ≤ x → x < exp 44 →
  hasPrimeOpen x (x + 1551)
/-- Consecutive-prime consumer of the uniform open interval. -/
def consecutive_gap_08768 : Prop := ∀ p q : ℕ,
  p.Prime → q.Prime → p < q → exp 24 ≤ (p : ℝ) →
  (∀ r : ℕ, p < r → r < q → ¬ r.Prime) →
    (q : ℝ) - p < (548 / 625) * sqrt (p : ℝ) * log (p : ℝ)

theorem challenge_late_open_08768 (hCMS : CMSCosineInput.v1.obstruction) (rh : RH.v1.hypothesis)
    (hJ : kernel_ratio_lower) : late_open_08768 :=
```

### RHOnePrimeEvolution.v1.uniform_open_08768

Conclusion: `IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:27`, SHA-256 `eb72cdde5f6b8dacdfc613a35f1e03b63b14a747274df83b97f57fbe0a1a6d89`. Proof: `Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean:55`, SHA-256 `72d85077cb5ff686a9061198c97a787b374032d955e405d6f678d20fa67635e2`.

```lean
def uniform_open_08768 : Prop := ∀ x : ℝ, exp 24 ≤ x →
  hasPrimeOpen x (x + (548 / 625) * sqrt x * log x)
/-- Bounded explicit improvement, not asymptotic domination of0.8358. -/
def finite_slab_open_08301 : Prop := ∀ x : ℝ, exp 44 ≤ x → x ≤ exp 59 →
  hasPrimeOpen x (x + (8301 / 10000) * sqrt x * log x)
/-- Absolute finite-range window, requiring no RH hypothesis. -/
def finite_absolute_1551 : Prop := ∀ x : ℝ, exp 24 ≤ x → x < exp 44 →
  hasPrimeOpen x (x + 1551)
/-- Consecutive-prime consumer of the uniform open interval. -/
def consecutive_gap_08768 : Prop := ∀ p q : ℕ,
  p.Prime → q.Prime → p < q → exp 24 ≤ (p : ℝ) →
  (∀ r : ℕ, p < r → r < q → ¬ r.Prime) →
    (q : ℝ) - p < (548 / 625) * sqrt (p : ℝ) * log (p : ℝ)

theorem challenge_uniform_open_08768 (hlate : late_open_08768)
    (hgap : PrimeGapTable.v1.gaps) : uniform_open_08768 :=
```

### RHOnePrimeEvolution.v1.finite_slab_open_08301

Conclusion: `IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:30`, SHA-256 `eb72cdde5f6b8dacdfc613a35f1e03b63b14a747274df83b97f57fbe0a1a6d89`. Proof: `Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean:62`, SHA-256 `72d85077cb5ff686a9061198c97a787b374032d955e405d6f678d20fa67635e2`.

```lean
def finite_slab_open_08301 : Prop := ∀ x : ℝ, exp 44 ≤ x → x ≤ exp 59 →
  hasPrimeOpen x (x + (8301 / 10000) * sqrt x * log x)
/-- Absolute finite-range window, requiring no RH hypothesis. -/
def finite_absolute_1551 : Prop := ∀ x : ℝ, exp 24 ≤ x → x < exp 44 →
  hasPrimeOpen x (x + 1551)
/-- Consecutive-prime consumer of the uniform open interval. -/
def consecutive_gap_08768 : Prop := ∀ p q : ℕ,
  p.Prime → q.Prime → p < q → exp 24 ≤ (p : ℝ) →
  (∀ r : ℕ, p < r → r < q → ¬ r.Prime) →
    (q : ℝ) - p < (548 / 625) * sqrt (p : ℝ) * log (p : ℝ)

theorem challenge_finite_slab_open_08301 (hCMS : CMSCosineInput.v1.obstruction)
    (rh : RH.v1.hypothesis) : finite_slab_open_08301 :=
```

### RHOnePrimeEvolution.v1.finite_absolute_1551

Conclusion: `IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:33`, SHA-256 `eb72cdde5f6b8dacdfc613a35f1e03b63b14a747274df83b97f57fbe0a1a6d89`. Proof: `Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean:67`, SHA-256 `72d85077cb5ff686a9061198c97a787b374032d955e405d6f678d20fa67635e2`.

```lean
def finite_absolute_1551 : Prop := ∀ x : ℝ, exp 24 ≤ x → x < exp 44 →
  hasPrimeOpen x (x + 1551)
/-- Consecutive-prime consumer of the uniform open interval. -/
def consecutive_gap_08768 : Prop := ∀ p q : ℕ,
  p.Prime → q.Prime → p < q → exp 24 ≤ (p : ℝ) →
  (∀ r : ℕ, p < r → r < q → ¬ r.Prime) →
    (q : ℝ) - p < (548 / 625) * sqrt (p : ℝ) * log (p : ℝ)

theorem challenge_finite_absolute_1551 (hgap : PrimeGapTable.v1.gaps) : finite_absolute_1551 :=
```

### RHOnePrimeEvolution.v1.consecutive_gap_08768

Conclusion: `IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:36`, SHA-256 `eb72cdde5f6b8dacdfc613a35f1e03b63b14a747274df83b97f57fbe0a1a6d89`. Proof: `Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean:71`, SHA-256 `72d85077cb5ff686a9061198c97a787b374032d955e405d6f678d20fa67635e2`.

```lean
def consecutive_gap_08768 : Prop := ∀ p q : ℕ,
  p.Prime → q.Prime → p < q → exp 24 ≤ (p : ℝ) →
  (∀ r : ℕ, p < r → r < q → ¬ r.Prime) →
    (q : ℝ) - p < (548 / 625) * sqrt (p : ℝ) * log (p : ℝ)

theorem challenge_consecutive_gap_08768 (hi : uniform_open_08768) :
    consecutive_gap_08768 :=
```

### RHOnePrimeEvolution.v1.continuous_late

Conclusion: `IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:42`, SHA-256 `eb72cdde5f6b8dacdfc613a35f1e03b63b14a747274df83b97f57fbe0a1a6d89`. Proof: `Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean:82`, SHA-256 `72d85077cb5ff686a9061198c97a787b374032d955e405d6f678d20fa67635e2`.

```lean
def continuous_late : Prop := ∀ x : ℝ, exp 44 ≤ x →
  hasPrimeOpen x (continuousEndpoint x)
/-- Strict comparison of entire endpoints on the complete real ray. -/
def continuous_improves_uniform : Prop := ∀ x : ℝ, exp 44 ≤ x →
  continuousEndpoint x < x + (548 / 625) * sqrt x * log x
/-- Hybrid finite/continuous frontier. No finite table is silently absorbed. -/
def continuous_uniform : Prop := ∀ x : ℝ, exp 24 ≤ x →
  hasPrimeOpen x (if x < exp 44 then x + 1551 else continuousEndpoint x)
/-- Bounded coefficient below0.8358, with BOTH endpoints open. Its finite upper
range must not be replaced by an asymptotic claim. -/
def bounded_open_08357 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 110 →
  hasPrimeOpen x (x + (8357 / 10000) * sqrt x * log x)
/-- Bounded strict-open comparison with the2026paper's FIXED0.85125 theorem;
this is not comparison with all retunings of that paper's full functions. -/
def bounded_open_08512 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 225 →
  hasPrimeOpen x (x + (532 / 625) * sqrt x * log x)
/-- Sharper first slab, including the separate finite computational bridge. -/
def bounded_open_08185 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 59 →
  hasPrimeOpen x (x + (1637 / 2000) * sqrt x * log x)

theorem challenge_continuous_late (hCMS : CMSCosineInput.v1.obstruction)
    (rh : RH.v1.hypothesis) : continuous_late :=
```

### RHOnePrimeEvolution.v1.continuous_improves_uniform

Conclusion: `IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:45`, SHA-256 `eb72cdde5f6b8dacdfc613a35f1e03b63b14a747274df83b97f57fbe0a1a6d89`. Proof: `Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean:87`, SHA-256 `72d85077cb5ff686a9061198c97a787b374032d955e405d6f678d20fa67635e2`.

```lean
def continuous_improves_uniform : Prop := ∀ x : ℝ, exp 44 ≤ x →
  continuousEndpoint x < x + (548 / 625) * sqrt x * log x
/-- Hybrid finite/continuous frontier. No finite table is silently absorbed. -/
def continuous_uniform : Prop := ∀ x : ℝ, exp 24 ≤ x →
  hasPrimeOpen x (if x < exp 44 then x + 1551 else continuousEndpoint x)
/-- Bounded coefficient below0.8358, with BOTH endpoints open. Its finite upper
range must not be replaced by an asymptotic claim. -/
def bounded_open_08357 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 110 →
  hasPrimeOpen x (x + (8357 / 10000) * sqrt x * log x)
/-- Bounded strict-open comparison with the2026paper's FIXED0.85125 theorem;
this is not comparison with all retunings of that paper's full functions. -/
def bounded_open_08512 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 225 →
  hasPrimeOpen x (x + (532 / 625) * sqrt x * log x)
/-- Sharper first slab, including the separate finite computational bridge. -/
def bounded_open_08185 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 59 →
  hasPrimeOpen x (x + (1637 / 2000) * sqrt x * log x)

theorem challenge_continuous_improves_uniform : continuous_improves_uniform :=
```

### RHOnePrimeEvolution.v1.continuous_uniform

Conclusion: `IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:48`, SHA-256 `eb72cdde5f6b8dacdfc613a35f1e03b63b14a747274df83b97f57fbe0a1a6d89`. Proof: `Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean:91`, SHA-256 `72d85077cb5ff686a9061198c97a787b374032d955e405d6f678d20fa67635e2`.

```lean
def continuous_uniform : Prop := ∀ x : ℝ, exp 24 ≤ x →
  hasPrimeOpen x (if x < exp 44 then x + 1551 else continuousEndpoint x)
/-- Bounded coefficient below0.8358, with BOTH endpoints open. Its finite upper
range must not be replaced by an asymptotic claim. -/
def bounded_open_08357 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 110 →
  hasPrimeOpen x (x + (8357 / 10000) * sqrt x * log x)
/-- Bounded strict-open comparison with the2026paper's FIXED0.85125 theorem;
this is not comparison with all retunings of that paper's full functions. -/
def bounded_open_08512 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 225 →
  hasPrimeOpen x (x + (532 / 625) * sqrt x * log x)
/-- Sharper first slab, including the separate finite computational bridge. -/
def bounded_open_08185 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 59 →
  hasPrimeOpen x (x + (1637 / 2000) * sqrt x * log x)

theorem challenge_continuous_uniform (hlate : continuous_late)
    (hgap : PrimeGapTable.v1.gaps) : continuous_uniform :=
```

### RHOnePrimeEvolution.v1.bounded_open_08357

Conclusion: `IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:52`, SHA-256 `eb72cdde5f6b8dacdfc613a35f1e03b63b14a747274df83b97f57fbe0a1a6d89`. Proof: `Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean:98`, SHA-256 `72d85077cb5ff686a9061198c97a787b374032d955e405d6f678d20fa67635e2`.

```lean
def bounded_open_08357 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 110 →
  hasPrimeOpen x (x + (8357 / 10000) * sqrt x * log x)
/-- Bounded strict-open comparison with the2026paper's FIXED0.85125 theorem;
this is not comparison with all retunings of that paper's full functions. -/
def bounded_open_08512 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 225 →
  hasPrimeOpen x (x + (532 / 625) * sqrt x * log x)
/-- Sharper first slab, including the separate finite computational bridge. -/
def bounded_open_08185 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 59 →
  hasPrimeOpen x (x + (1637 / 2000) * sqrt x * log x)

theorem challenge_bounded_open_08357 (hCMS : CMSCosineInput.v1.obstruction)
    (rh : RH.v1.hypothesis) (hgap : PrimeGapTable.v1.gaps) : bounded_open_08357 :=
```

### RHOnePrimeEvolution.v1.bounded_open_08512

Conclusion: `IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:56`, SHA-256 `eb72cdde5f6b8dacdfc613a35f1e03b63b14a747274df83b97f57fbe0a1a6d89`. Proof: `Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean:105`, SHA-256 `72d85077cb5ff686a9061198c97a787b374032d955e405d6f678d20fa67635e2`.

```lean
def bounded_open_08512 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 225 →
  hasPrimeOpen x (x + (532 / 625) * sqrt x * log x)
/-- Sharper first slab, including the separate finite computational bridge. -/
def bounded_open_08185 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 59 →
  hasPrimeOpen x (x + (1637 / 2000) * sqrt x * log x)

theorem challenge_bounded_open_08512 (hCMS : CMSCosineInput.v1.obstruction)
    (rh : RH.v1.hypothesis) (hgap : PrimeGapTable.v1.gaps) : bounded_open_08512 :=
```

### RHOnePrimeEvolution.v1.bounded_open_08185

Conclusion: `IEANTN/Nodes/RHOnePrimeEvolution/v1/Conclusions.lean:59`, SHA-256 `eb72cdde5f6b8dacdfc613a35f1e03b63b14a747274df83b97f57fbe0a1a6d89`. Proof: `Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean:112`, SHA-256 `72d85077cb5ff686a9061198c97a787b374032d955e405d6f678d20fa67635e2`.

```lean
def bounded_open_08185 : Prop := ∀ x : ℝ, exp 24 ≤ x → x ≤ exp 59 →
  hasPrimeOpen x (x + (1637 / 2000) * sqrt x * log x)

theorem challenge_bounded_open_08185 (hCMS : CMSCosineInput.v1.obstruction)
    (rh : RH.v1.hypothesis) (hgap : PrimeGapTable.v1.gaps) : bounded_open_08185 :=
```

### PrimePowerPopulation.v1.cube_population_all_real

Conclusion: `IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean:12`, SHA-256 `f1bdbcabd266bf3f3cd3c99bb54f9d7caccfa416444ad698a3e793fdb8f55c7e`. Proof: `Solutions/PrimePowerPopulation.v1/Solution.lean:18`, SHA-256 `380909141429f997d1a49cd9540488d0c7b203e0120cce6bb3b77fbcf73a4532`.

```lean
def cube_population_all_real : Prop := ∀ n : ℝ, exp 8 ≤ n →
  (101797 / 20000 + (7 / 5) / log n) * n * sqrt n <
    ((primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ)

theorem challenge_cube_population_all_real
    (h : PrimeInterval.v4.optimized_strict_family) : cube_population_all_real :=
```

### PrimePowerPopulation.v1.cube_density_all_real

Conclusion: `IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean:18`, SHA-256 `f1bdbcabd266bf3f3cd3c99bb54f9d7caccfa416444ad698a3e793fdb8f55c7e`. Proof: `Solutions/PrimePowerPopulation.v1/Solution.lean:23`, SHA-256 `380909141429f997d1a49cd9540488d0c7b203e0120cce6bb3b77fbcf73a4532`.

```lean
def cube_density_all_real : Prop := ∀ n : ℝ, exp 8 ≤ n →
  (7 / 10) * n ^ 2 / log n < ((primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ)

theorem challenge_cube_density_all_real
    (h : PrimeInterval.v4.optimized_strict_family) : cube_density_all_real :=
```

### PrimePowerPopulation.v1.cube_density_natural

Conclusion: `IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean:23`, SHA-256 `f1bdbcabd266bf3f3cd3c99bb54f9d7caccfa416444ad698a3e793fdb8f55c7e`. Proof: `Solutions/PrimePowerPopulation.v1/Solution.lean:28`, SHA-256 `380909141429f997d1a49cd9540488d0c7b203e0120cce6bb3b77fbcf73a4532`.

```lean
def cube_density_natural : Prop := ∀ n : ℕ, 2981 ≤ n →
  (7 / 10) * (n : ℝ) ^ 2 / log n <
    ((primesBetween ((n : ℝ) ^ 3) (((n : ℝ) + 1) ^ 3)).card : ℝ)

theorem challenge_cube_density_natural
    (h : PrimeInterval.v4.optimized_strict_family) : cube_density_natural :=
```

### PrimePowerPopulation.v1.higher_power_population

Conclusion: `IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean:29`, SHA-256 `f1bdbcabd266bf3f3cd3c99bb54f9d7caccfa416444ad698a3e793fdb8f55c7e`. Proof: `Solutions/PrimePowerPopulation.v1/Solution.lean:33`, SHA-256 `380909141429f997d1a49cd9540488d0c7b203e0120cce6bb3b77fbcf73a4532`.

```lean
def higher_power_population : Prop := ∀ n : ℝ, exp 8 ≤ n → ∀ r : ℕ, 3 ≤ r →
  (101797 / 20000 + (21 / 5) / ((r : ℝ) * log n)) * sqrt (n ^ r) <
    ((primesBetween (n ^ r) ((n + 1) ^ r)).card : ℝ)

theorem challenge_higher_power_population
    (h : PrimeInterval.v4.optimized_strict_family) : higher_power_population :=
```

### PrimePowerPopulation.v1.cube_frontier

Conclusion: `IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean:35`, SHA-256 `f1bdbcabd266bf3f3cd3c99bb54f9d7caccfa416444ad698a3e793fdb8f55c7e`. Proof: `Solutions/PrimePowerPopulation.v1/Solution.lean:42`, SHA-256 `380909141429f997d1a49cd9540488d0c7b203e0120cce6bb3b77fbcf73a4532`.

```lean
def cube_frontier : Prop := ∀ n : ℝ, exp 8 ≤ n →
  max ((101797 / 20000 + (7 / 5) / log n) * n * sqrt n)
    ((7 / 10) * n ^ 2 / log n) <
    ((primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ)

theorem challenge_cube_frontier
    (h : PrimeInterval.v4.optimized_strict_family) : cube_frontier :=
```

### PrimePowerPopulation.v1.density_improves_648

Conclusion: `IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean:42`, SHA-256 `f1bdbcabd266bf3f3cd3c99bb54f9d7caccfa416444ad698a3e793fdb8f55c7e`. Proof: `Solutions/PrimePowerPopulation.v1/Solution.lean:47`, SHA-256 `380909141429f997d1a49cd9540488d0c7b203e0120cce6bb3b77fbcf73a4532`.

```lean
def density_improves_648 : Prop := ∀ n : ℝ, exp 8 ≤ n →
  (81 / 125) * n ^ 2 / log n < (7 / 10) * n ^ 2 / log n

theorem challenge_density_improves_648 : density_improves_648 :=
```

### Goldbach.v3.sorted_count_extended

Conclusion: `IEANTN/Nodes/Goldbach/v3/Conclusions.lean:16`, SHA-256 `fd83211aa68e3c9aee796319aa1bc507efbb345166a2b6d7b926e67d43b91c02`. Proof: `Solutions/RHOnePrimeEvolution.v1/frontier/GoldbachV3Consumer.lean:11`, SHA-256 `ac793afa19c10f0f4f956444dc52e68a8fc9eb94d3e66794cc12d1fdc6ee91f6`.

```lean
def sorted_count_extended : Prop := ∀ H n : ℕ, GoldbachEvenUpTo H → Odd n →
  3 * H ≤ 2 * n → exp 24 ≤ (n : ℝ) - H →
  (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4 →
  (1 / 2 + (21 / 10) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
    ((GoldbachCounts.sortedTriples n).card : ℝ)

theorem challenge_sorted_count_extended
    (hi : PrimeInterval.v4.optimized_strict_family) : sorted_count_extended :=
```

### Goldbach.v3.sorted_count_full_finite_range

Conclusion: `IEANTN/Nodes/Goldbach/v3/Conclusions.lean:24`, SHA-256 `fd83211aa68e3c9aee796319aa1bc507efbb345166a2b6d7b926e67d43b91c02`. Proof: `Solutions/RHOnePrimeEvolution.v1/frontier/GoldbachV3Consumer.lean:16`, SHA-256 `ac793afa19c10f0f4f956444dc52e68a8fc9eb94d3e66794cc12d1fdc6ee91f6`.

```lean
def sorted_count_full_finite_range : Prop := ∀ H n : ℕ, GoldbachEvenUpTo H → Odd n →
  exp 24 ≤ (n : ℝ) - H →
  (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4 →
  (1 / 3 + (7 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
    ((GoldbachCounts.sortedTriples n).card : ℝ)

theorem challenge_sorted_count_full_finite_range
    (hi : PrimeInterval.v4.optimized_strict_family) : sorted_count_full_finite_range :=
```

### Goldbach.v3.sorted_count_750m_band

Conclusion: `IEANTN/Nodes/Goldbach/v3/Conclusions.lean:34`, SHA-256 `fd83211aa68e3c9aee796319aa1bc507efbb345166a2b6d7b926e67d43b91c02`. Proof: `Solutions/RHOnePrimeEvolution.v1/frontier/GoldbachV3Consumer.lean:21`, SHA-256 `ac793afa19c10f0f4f956444dc52e68a8fc9eb94d3e66794cc12d1fdc6ee91f6`.

```lean
def sorted_count_750m_band : Prop := GoldbachEvenUpTo 4000000000000000000 →
  ∀ n : ℕ, Odd n → 6000000000000000000 ≤ n → n ≤ 8000000000000000000 →
    (750000000 : ℝ) < ((GoldbachCounts.sortedTriples n).card : ℝ)

theorem challenge_sorted_count_750m_band
    (hi : PrimeInterval.v4.optimized_strict_family) : sorted_count_750m_band :=
```

### PrimeQuantile.v4.strict_generic_block

Conclusion: `IEANTN/Nodes/PrimeQuantile/v4/Conclusions.lean:14`, SHA-256 `db64e780db69d57d4b4ce39de6d2b027f13494581109fab46cd77e3db354eaa8`. Proof: `Solutions/RHOnePrimeEvolution.v1/frontier/PrimeQuantileV4Consumer.lean:11`, SHA-256 `2f14d267ff84bd3878d724843d4e06b1a5890965ea28be135444836f2da824be`.

```lean
def strict_generic_block : Prop := ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16,
  ∀ x : ℝ, exp 24 ≤ x → ∀ m : ℕ,
    (m : ℝ) ≤ (8 / 9 * C - 18203 / 20000 + (21 / 5) / log x) * sqrt x →
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
        x + C * sqrt x * log x

theorem challenge_strict_generic_block
    (hi : PrimeInterval.v4.optimized_strict_family) : strict_generic_block :=
```

### PrimeQuantile.v4.strict_special_block

Conclusion: `IEANTN/Nodes/PrimeQuantile/v4/Conclusions.lean:23`, SHA-256 `db64e780db69d57d4b4ce39de6d2b027f13494581109fab46cd77e3db354eaa8`. Proof: `Solutions/RHOnePrimeEvolution.v1/frontier/PrimeQuantileV4Consumer.lean:16`, SHA-256 `2f14d267ff84bd3878d724843d4e06b1a5890965ea28be135444836f2da824be`.

```lean
def strict_special_block : Prop := ∀ x : ℝ, exp 24 ≤ x → ∀ m : ℕ,
  (m : ℝ) ≤ (180173 / 180000 + (29 / 5) / log x) * sqrt x →
  x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
    (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
      x + (43 / 20) * sqrt x * log x

theorem challenge_strict_special_block
    (hi : PrimeInterval.v4.optimized_strict_215) : strict_special_block :=
```

### PrimeQuantile.v4.shifted_sqrt_block

Conclusion: `IEANTN/Nodes/PrimeQuantile/v4/Conclusions.lean:32`, SHA-256 `db64e780db69d57d4b4ce39de6d2b027f13494581109fab46cd77e3db354eaa8`. Proof: `Solutions/RHOnePrimeEvolution.v1/frontier/PrimeQuantileV4Consumer.lean:22`, SHA-256 `2f14d267ff84bd3878d724843d4e06b1a5890965ea28be135444836f2da824be`.

```lean
def shifted_sqrt_block : Prop := ∀ x : ℝ, exp 24 ≤ x → ∀ m : ℕ,
  (m : ℝ) ≤ sqrt x →
  x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
    (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
      x + (343827 / 160000) * sqrt x * log x - (189 / 40) * sqrt x

theorem challenge_shifted_sqrt_block
    (hi : PrimeInterval.v4.optimized_strict_family) : shifted_sqrt_block :=
```

## Separate external input nodes

- CMSCosineInput.v1.obstruction: the named CMS analytic no-prime inequality; B, literature-backed, not newly proved in Mathlib. The equation/entire-extension qualification is documented in analytic/SOURCE_REMOVABLE_EXTENSION.md.
- PrimeGapTable.v1.gaps: reported historical gap computation below2^64 with maximal gap1550; asserted input, not kernel-verified nor source-first PV. Only the new consequence and terminal-prime proof are D.

## Additional proved comparison/support lemmas

- Actual sine integral and sharper quotient: comparisons/CMSKernelNumerics.lean, analytic/CMSJSharper.lean.
- TerminalPrime.lean:3Lucas certificates, Std3. No empty-axiom claim.
- PopulationFrontier.lean: exact α tradeoff, strict limiting ε margin, shifted width, actual prime-index conversion.
- WholePopulationComparison2026.lean: exact comparison with the two PRINTED 2026 curves; not global population optimality. RetunedPublishedScalar.lean: conservative scalar positivity for all44≤L≤60; not the complete retuned prime theorem.
- Lee2023LiteralRow.lean: negative literal Table4 right side in each written version at exp10. This does not prove a corrected prime bound.

## Non-theorem experiments and negative results

Gaussian/hat objective enclosures, adaptive/SOS attempts, and possible extensions of2026population comparisons remain external E or written proposals. No experiment row is silently promoted to a verified numerical node. The full-function2026retuning and Lee2026wide-window estimate prevent a global winner claim. No new Ramanujan experiment or causal exposure conclusion is part of this campaign.
