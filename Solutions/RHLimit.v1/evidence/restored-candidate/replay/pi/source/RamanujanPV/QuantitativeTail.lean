/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao, OpenAI (Codex)
-/
import Mathlib
import RamanujanPV.Intervals
import IEANTN.Nodes.DudekPlatt.v3.Conclusions
import IEANTN.Nodes.DudekPlattNumerics.v6.Conclusions

/-! A genuinely proved quantitative tail from the existing actual-pi expansion.
The old mathematical proof source is reproduced below with namespace-only changes;
no application proof object is reused. The 144 expansion remains an explicit analytic
input until its QRH/density derivation is rebuilt in this clean context. -/
-- Exact mathematical source copy, namespace-only adaptation: Solutions/DudekPlatt.v3/Shifts.lean
/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The two shift estimates

Both express `1/(log x − 1)^k` in terms of `1/(log x)^k`, and between them they are the whole
content of the erratum in Dudek–Platt's Lemma 2.1.

`shift_factorial_lower` handles the terms with positive coefficients `k!`, where a **lower** bound
on `1/(l−1)^{k+1}` is what is wanted, and the paper's own truncation argument is sound.

`shift_m_lower_of_nonpos` handles the term carrying `m`, where the paper applies the same lower
bound — valid only for `m  ≥  0`, and `m` is negative in every application. Bounding
`1/(l−1)^6` from **above** instead, by `(1 + 1/log xₐ)^6 / l^6`, is what makes the argument go
through for negative `m`, and the extra factor `(1 + 1/log xₐ)^6 > 1` is the difference between
`DudekPlatt.v3.εPos` and `DudekPlatt.v3.εNeg`.

Following `PrimeNumberTheoremAnd`'s `Ramanujan.shift_factorial_lower` and
`Ramanujan.shift_m_lower_of_nonpos`, which carry the same repair.
-/

open Real

namespace RamanujanPV.RepairedBounds

/-- The positive-coefficient shift. Purely algebraic: the difference is a quotient whose numerator
is a polynomial in `l − 1` with non-negative coefficients. -/
lemma shift_factorial_lower (l : ℝ) (hl : 1 < l) :
    1 / l * (1 / (l - 1) + 1 / (l - 1) ^ 2 + 2 / (l - 1) ^ 3
        + 6 / (l - 1) ^ 4 + 24 / (l - 1) ^ 5)
       ≥  1 / l ^ 2 + 2 / l ^ 3 + 5 / l ^ 4 + 16 / l ^ 5 + 65 / l ^ 6
        + (206 + 364 / l + 381 / l ^ 2 + 238 / l ^ 3
            + 97 / l ^ 4 + 30 / l ^ 5 + 8 / l ^ 6) / l ^ 7 := by
  have hl0 : 0 < l := by linarith
  have hlm1 : 0 < l - 1 := by linarith
  have hdiff :
      1 / l *
          (1 / (l - 1) + 1 / (l - 1) ^ 2 + 2 / (l - 1) ^ 3 + 6 / (l - 1) ^ 4 + 24 / (l - 1) ^ 5)
        - (1 / l ^ 2 + 2 / l ^ 3 + 5 / l ^ 4 + 16 / l ^ 5 + 65 / l ^ 6 +
            (206 + 364 / l + 381 / l ^ 2 + 238 / l ^ 3 + 97 / l ^ 4 + 30 / l ^ 5 + 8 / l ^ 6)
              / l ^ 7)
      = (153 * (l - 1) ^ 10 + 1484 * (l - 1) ^ 9 + 6249 * (l - 1) ^ 8 + 14886 * (l - 1) ^ 7 +
          22027 * (l - 1) ^ 6 + 21083 * (l - 1) ^ 5 + 13345 * (l - 1) ^ 4 + 5701 * (l - 1) ^ 3 +
          1658 * (l - 1) ^ 2 + 294 * (l - 1) + 24) / (l ^ 13 * (l - 1) ^ 5) := by
    field_simp [hl0.ne', hlm1.ne']
    ring
  have hnum_nonneg :
      0  ≤  153 * (l - 1) ^ 10 + 1484 * (l - 1) ^ 9 + 6249 * (l - 1) ^ 8 + 14886 * (l - 1) ^ 7 +
          22027 * (l - 1) ^ 6 + 21083 * (l - 1) ^ 5 + 13345 * (l - 1) ^ 4 + 5701 * (l - 1) ^ 3 +
          1658 * (l - 1) ^ 2 + 294 * (l - 1) + 24 := by
    positivity
  have hden_pos : 0 < l ^ 13 * (l - 1) ^ 5 := by positivity
  have hdelta_nonneg :
      0  ≤  1 / l *
            (1 / (l - 1) + 1 / (l - 1) ^ 2 + 2 / (l - 1) ^ 3 + 6 / (l - 1) ^ 4 + 24 / (l - 1) ^ 5)
          - (1 / l ^ 2 + 2 / l ^ 3 + 5 / l ^ 4 + 16 / l ^ 5 + 65 / l ^ 6 +
              (206 + 364 / l + 381 / l ^ 2 + 238 / l ^ 3 + 97 / l ^ 4 + 30 / l ^ 5 + 8 / l ^ 6)
                / l ^ 7) := by
    rw [hdiff]
    exact div_nonneg hnum_nonneg hden_pos.le
  linarith

/-- **The repair.** For `m  ≤  0`, the correct lower bound on `m / (l (l−1)^6)` uses `(1 + 1/log xₐ)^6`
rather than `1`.

The step is: `l/(l−1)  ≤  1 + 1/log xₐ` whenever `log xₐ + 1  ≤  l`, so raising to the sixth power and
multiplying by the *non-positive* `m / l^7` reverses the inequality — which is exactly the direction
a lower bound needs, and exactly what the paper's uniform use of the truncation misses. -/
lemma shift_m_lower_of_nonpos (m xₐ l : ℝ) (hm : m  ≤  0) (hxₐ : 0 < log xₐ)
    (hl : log xₐ + 1  ≤  l) :
    m / (l * (l - 1) ^ 6)  ≥  ((1 + 1 / log xₐ) ^ 6 * m) / l ^ 7 := by
  have hlm1_pos : 0 < l - 1 := by linarith
  have hl_pos : 0 < l := by linarith
  have hbase : l / (l - 1)  ≤  1 + 1 / log xₐ := by
    have hlog_le : log xₐ  ≤  l - 1 := by linarith
    have hsum : 1 + 1 / (l - 1)  ≤  1 + 1 / log xₐ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (one_div_le_one_div_of_le hxₐ hlog_le) 1
    have hratio : l / (l - 1) = 1 + 1 / (l - 1) := by
      field_simp [hlm1_pos.ne']
      ring
    simpa [hratio] using hsum
  have hleft : m / (l * (l - 1) ^ 6) = (m / l ^ 7) * (l / (l - 1)) ^ 6 := by
    field_simp [hl_pos.ne', hlm1_pos.ne']
  have hright : ((1 + 1 / log xₐ) ^ 6 * m) / l ^ 7 = (m / l ^ 7) * (1 + 1 / log xₐ) ^ 6 := by
    ring
  rw [hleft, hright]
  exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (by positivity) hbase 6)
    (div_nonpos_of_nonpos_of_nonneg hm (pow_nonneg hl_pos.le _))

/-- The positive-`m` counterpart, for completeness: when `0  ≤  m` the paper's own direction is
correct, and no `(1 + 1/log xₐ)^6` factor is needed. `εLower` selects between this branch and the
one above, which is the whole of the repair. -/
lemma shift_m_lower_of_nonneg (m l : ℝ) (hm : 0  ≤  m) (hl : 1 < l) :
    m / (l * (l - 1) ^ 6)  ≥  m / l ^ 7 := by
  have hl0 : 0 < l := by linarith
  have hlm1 : 0 < l - 1 := by linarith
  have hratio_ge1 : 1  ≤  l / (l - 1) := (le_div_iff₀ hlm1).2 (by linarith)
  have hpow : 1  ≤  (l / (l - 1)) ^ 6 := one_le_pow₀ hratio_ge1
  have hmdiv_nonneg : 0  ≤  m / l ^ 7 := div_nonneg hm (pow_nonneg hl0.le _)
  have hmul : m / l ^ 7  ≤  (m / l ^ 7) * (l / (l - 1)) ^ 6 := by
    simpa [one_mul] using mul_le_mul_of_nonneg_left hpow hmdiv_nonneg
  have hrepr : m / (l * (l - 1) ^ 6) = (m / l ^ 7) * (l / (l - 1)) ^ 6 := by
    field_simp [hl0.ne', hlm1.ne']
  rw [hrepr]
  exact hmul

end RamanujanPV.RepairedBounds

-- Exact mathematical source copy, namespace-only adaptation: Solutions/DudekPlatt.v3/Bounds.lean
/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The two bounds the criterion combines

`sq_pi_lt` squares the upper estimate for `π(x)`; `ex_pi_gt` applies the lower estimate at `x/e`
and rescales. Their difference is a single quotient over `(log x)^7`, and the criterion's
hypothesis is exactly what makes that quotient negative.

`ex_pi_gt` splits on the sign of `m`, and that split is the erratum: the `nonneg` branch is the
paper's own argument, and the `neg` branch — the one every application actually needs — uses
`RamanujanPV.RepairedBounds.shift_m_lower_of_nonpos` in place of the truncation the paper reuses there.

The mathematics is `PrimeNumberTheoremAnd`'s, from its `Ramanujan` namespace. Only the vocabulary
differs: its `pi` is this repository's `IEANTN.primeCounting` — the same definition,
`Nat.primeCounting ⌊x⌋₊` — and its `ε`, `ε'`, `εneg`, `εlower` are this node's `εUpper`, `εPos`,
`εNeg`, `εLower`.
-/

open Real IEANTN DudekPlatt.v3

namespace RamanujanPV.RepairedBounds

theorem sq_pi_lt (M_a x_a : ℝ) (hupper : ∀ x > x_a, primeCounting x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6)) :
    ∀ x > x_a, primeCounting x ^ 2 < x ^ 2 * (1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 64 / log x ^ 6 + εUpper M_a x / log x ^ 7) := by
  intro x hx
  have sq_algebra (M l : ℝ) : ((Nat.factorial 0 : ℝ) / l ^ 1 + (Nat.factorial 1 : ℝ) / l ^ 2 + (Nat.factorial 2 : ℝ) / l ^ 3 + (Nat.factorial 3 : ℝ) / l ^ 4 + (Nat.factorial 4 : ℝ) / l ^ 5 + M / l ^ 6) ^ 2
    = 1 / l ^ 2 + 2 / l ^ 3 + 5 / l ^ 4 + 16 / l ^ 5 + 64 / l ^ 6 + (72 + 2 * M + (2 * M + 132) / l + (4 * M + 288) / l ^ 2 + (12 * M + 576) / l ^ 3 + (48 * M) / l ^ 4 + M ^ 2 / l ^ 5) / l ^ 7 := by
    ring
  have h_nonneg_pi : 0  ≤  primeCounting x := by
    unfold IEANTN.primeCounting
    exact_mod_cast Nat.zero_le (⌊x⌋₊.primeCounting)
  have h_pos_rhs : 0 < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6) := by
    linarith [h_nonneg_pi, hupper x hx]
  have h_sum_eq : ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) = (Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  have h_main1 : ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) ^ 2 = 1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 64 / log x ^ 6 + εUpper M_a x / log x ^ 7 := by
    simpa [εUpper] using sq_algebra M_a (log x)
  have h_eq : x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) = x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6) := by
    rw [h_sum_eq]; ring
  have h1'' : primeCounting x < x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) := by
    simpa only [h_eq] using hupper x hx
  have h_pos1 : 0 < x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) := by
    simpa only [h_eq] using h_pos_rhs
  have h2 : primeCounting x ^ 2 < (x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6)) ^ 2 :=
    sq_lt_sq.mpr (by simpa only [abs_of_nonneg h_nonneg_pi, abs_of_pos h_pos1] using h1'')
  have h4 : (x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6)) ^ 2 = x ^ 2 * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) ^ 2 := by ring
  simpa only [h4, h_main1] using h2

theorem ex_pi_gt_nonneg
    (m_a x_a : ℝ)
    (hm : 0  ≤  m_a)
    (hlower : ∀ x > x_a,
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
        + (m_a * x / log x ^ 6) < primeCounting x) :
    ∀ x > exp 1 * x_a,
      exp 1 * x / log x * primeCounting (x / exp 1) >
        x ^ 2 * (
          1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5
          + 65 / log x ^ 6 + εPos m_a x / log x ^ 7) := by
  intro x hx
  have hxa_ge_one : 1  ≤  x_a := by
    by_contra hxa
    have hlt : x_a < 1 := lt_of_not_ge hxa
    have hbad := hlower 1 hlt
    have hpi1 : primeCounting 1 = 0 := by
      unfold IEANTN.primeCounting
      norm_num
    have hleft0 :
        (1 : ℝ) * ∑ k ∈ Finset.range 5, (k.factorial / log (1 : ℝ) ^ (k + 1))
          + (m_a * (1 : ℝ) / log (1 : ℝ) ^ 6) = 0 := by
      norm_num
    linarith
  have hxe : exp 1 < x := by
    have h1 : exp 1  ≤  exp 1 * x_a := by
      nlinarith [hxa_ge_one, exp_pos (1 : ℝ)]
    grind
  have hlog_gt1 : 1 < log x := by
    simpa using log_lt_log (show 0 < exp 1 by positivity) hxe
  have hlog_pos : 0 < log x := by linarith
  have hx_pos : 0 < x := lt_trans (exp_pos 1) hxe
  have hy_gt : x / exp 1 > x_a := by
    have hmul : x_a * exp 1 < x := by simpa [mul_comm] using hx
    exact (lt_div_iff₀ (exp_pos 1)).2 hmul
  have hlow := hlower (x / exp 1) hy_gt
  have hmul_pos : 0 < exp 1 * x / log x :=
    div_pos (mul_pos (exp_pos 1) hx_pos) hlog_pos
  have hmul := mul_lt_mul_of_pos_left hlow hmul_pos
  have hlog_div : log (x / exp 1) = log x - 1 := by
    rw [log_div (show x ≠ 0 by linarith) (show exp 1 ≠ 0 by positivity), log_exp]
  have hfrom0 :
      exp 1 * x / log x *
        ((x / exp 1) * ∑ k ∈ Finset.range 5, (k.factorial / (log x - 1) ^ (k + 1))
          + (m_a * (x / exp 1) / (log x - 1) ^ 6))
      < exp 1 * x / log x * primeCounting (x / exp 1) := by
    simpa [hlog_div] using hmul
  let S : ℝ := ∑ k ∈ Finset.range 5, (k.factorial / (log x - 1) ^ (k + 1))
  have hfrom :
      x ^ 2 * ((1 / log x) * (S + m_a / (log x - 1) ^ 6))
      < exp 1 * x / log x * primeCounting (x / exp 1) := by
    have hleft :
        exp 1 * x / log x * ((x / exp 1) * S + (m_a * (x / exp 1) / (log x - 1) ^ 6))
        = x ^ 2 * ((1 / log x) * (S + m_a / (log x - 1) ^ 6)) := by
      field_simp [hlog_pos.ne', show (exp 1 : ℝ) ≠ 0 by positivity]
    simpa [S, hleft] using hfrom0
  have hsum :
      S =
        1 / (log x - 1) + 1 / (log x - 1) ^ 2 + 2 / (log x - 1) ^ 3 +
        6 / (log x - 1) ^ 4 + 24 / (log x - 1) ^ 5 := by
    dsimp [S]
    simp [Finset.sum_range_succ, Nat.factorial]
  have hfac :
      (1 / log x) * S
       ≥ 
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
            30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7 := by
    simpa [hsum] using shift_factorial_lower (log x) hlog_gt1
  have hmterm :
      m_a / (log x * (log x - 1) ^ 6)
       ≥  m_a / log x ^ 7 := by
    simpa using shift_m_lower_of_nonneg m_a (log x) hm hlog_gt1
  have hcore65 :
      (1 / log x) * (S + m_a / (log x - 1) ^ 6)
       ≥ 
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + εPos m_a x / log x ^ 7 := by
    have hsplit :
        (1 / log x) * (S + m_a / (log x - 1) ^ 6)
        = (1 / log x) * S + m_a / (log x * (log x - 1) ^ 6) := by
      calc
        (1 / log x) * (S + m_a / (log x - 1) ^ 6)
            = (1 / log x) * S + (1 / log x) * (m_a / (log x - 1) ^ 6) := by ring
        _ = (1 / log x) * S + m_a / (log x * (log x - 1) ^ 6) := by
          field_simp [hlog_pos.ne']
    have hsum' := add_le_add hfac hmterm
    have hsum'' :
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
          + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
          + m_a / log x ^ 7
         ≤  (1 / log x) * (S + m_a / (log x - 1) ^ 6) := by
      calc
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
          + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
          + m_a / log x ^ 7
             ≤  (1 / log x) * S + m_a / (log x * (log x - 1) ^ 6) := hsum'
        _ = (1 / log x) * (S + m_a / (log x - 1) ^ 6) := hsplit.symm
    calc
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + εPos m_a x / log x ^ 7
          =
            1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
              + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
                  30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
              + m_a / log x ^ 7 := by
                simp [εPos]
                ring
      _  ≤  (1 / log x) * (S + m_a / (log x - 1) ^ 6) := hsum''
  have htarget_le :
      x ^ 2 *
          (1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            εPos m_a x / log x ^ 7)
       ≤  x ^ 2 * ((1 / log x) * (S + m_a / (log x - 1) ^ 6)) :=
    mul_le_mul_of_nonneg_left hcore65 (sq_nonneg x)
  grind

theorem ex_pi_gt_neg
    (m xₐ : ℝ)
    (hm : m  ≤  0)
    (hxₐ : 1 < xₐ)
    (hlower : ∀ x > xₐ,
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
        + (m * x / log x ^ 6) < primeCounting x) :
    ∀ x > exp 1 * xₐ,
      exp 1 * x / log x * primeCounting (x / exp 1) >
        x ^ 2 * (
          1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5
          + 65 / log x ^ 6 + εNeg m xₐ x / log x ^ 7) := by
  intro x hx
  have hxe : exp 1 < x := by
    have h1 : exp 1  ≤  exp 1 * xₐ := by
      nlinarith [hxₐ, exp_pos (1 : ℝ)]
    grind
  have hlog_gt1 : 1 < log x := by
    simpa using log_lt_log (show 0 < exp 1 by positivity) hxe
  have hlog_pos : 0 < log x := by linarith
  have hx_pos : 0 < x := lt_trans (exp_pos 1) hxe
  have hy_gt : x / exp 1 > xₐ := by
    have hmul : xₐ * exp 1 < x := by simpa [mul_comm] using hx
    exact (lt_div_iff₀ (exp_pos 1)).2 hmul
  have hlow := hlower (x / exp 1) hy_gt
  have hmul_pos : 0 < exp 1 * x / log x :=
    div_pos (mul_pos (exp_pos 1) hx_pos) hlog_pos
  have hmul := mul_lt_mul_of_pos_left hlow hmul_pos
  have hlog_div : log (x / exp 1) = log x - 1 := by
    rw [log_div (show x ≠ 0 by linarith) (show exp 1 ≠ 0 by positivity), log_exp]
  have hfrom0 :
      exp 1 * x / log x *
        ((x / exp 1) * ∑ k ∈ Finset.range 5, (k.factorial / (log x - 1) ^ (k + 1))
          + (m * (x / exp 1) / (log x - 1) ^ 6))
      < exp 1 * x / log x * primeCounting (x / exp 1) := by
    simpa [hlog_div] using hmul
  let S : ℝ := ∑ k ∈ Finset.range 5, (k.factorial / (log x - 1) ^ (k + 1))
  have hfrom :
      x ^ 2 * ((1 / log x) * (S + m / (log x - 1) ^ 6))
      < exp 1 * x / log x * primeCounting (x / exp 1) := by
    have hleft :
        exp 1 * x / log x * ((x / exp 1) * S + (m * (x / exp 1) / (log x - 1) ^ 6))
        = x ^ 2 * ((1 / log x) * (S + m / (log x - 1) ^ 6)) := by
      field_simp [hlog_pos.ne', show (exp 1 : ℝ) ≠ 0 by positivity]
    simpa [S, hleft] using hfrom0
  have hsum :
      S =
        1 / (log x - 1) + 1 / (log x - 1) ^ 2 + 2 / (log x - 1) ^ 3 +
        6 / (log x - 1) ^ 4 + 24 / (log x - 1) ^ 5 := by
    dsimp [S]
    simp [Finset.sum_range_succ, Nat.factorial]
  have hfac :
      (1 / log x) * S
       ≥ 
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
            30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7 := by
    simpa [hsum] using shift_factorial_lower (log x) hlog_gt1
  have hxₐ_log_pos : 0 < log xₐ := log_pos hxₐ
  have hlogxₐ_le : log xₐ + 1  ≤  log x := by
    have hmul : exp 1 * xₐ < x := by simpa [mul_comm] using hx
    have hlog := log_lt_log (show 0 < exp 1 * xₐ by positivity) hmul
    have hlog_mul : log (exp 1 * xₐ) = log xₐ + 1 := by
      rw [log_mul (by positivity) (by positivity), log_exp]
      ring
    linarith
  have hmterm :
      m / (log x * (log x - 1) ^ 6)
       ≥  ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7 := by
    simpa using shift_m_lower_of_nonpos m xₐ (log x) hm hxₐ_log_pos hlogxₐ_le
  have hcore :
      (1 / log x) * (S + m / (log x - 1) ^ 6)
       ≥ 
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + εNeg m xₐ x / log x ^ 7 := by
    have hsplit :
        (1 / log x) * (S + m / (log x - 1) ^ 6)
        = (1 / log x) * S + m / (log x * (log x - 1) ^ 6) := by
      calc
        (1 / log x) * (S + m / (log x - 1) ^ 6)
            = (1 / log x) * S + (1 / log x) * (m / (log x - 1) ^ 6) := by ring
        _ = (1 / log x) * S + m / (log x * (log x - 1) ^ 6) := by
          field_simp [hlog_pos.ne']
    have hsum' := add_le_add hfac hmterm
    have hsum'' :
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
          + ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7
         ≤  (1 / log x) * (S + m / (log x - 1) ^ 6) := by
      calc
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
          + ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7
             ≤  (1 / log x) * S + m / (log x * (log x - 1) ^ 6) := hsum'
        _ = (1 / log x) * (S + m / (log x - 1) ^ 6) := hsplit.symm
    calc
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
          εNeg m xₐ x / log x ^ 7
          =
            1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
              (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
                30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
              + ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7 := by
                simp [εNeg]
                ring
      _  ≤  (1 / log x) * (S + m / (log x - 1) ^ 6) := hsum''
  have htarget_le :
      x ^ 2 *
          (1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            εNeg m xₐ x / log x ^ 7)
       ≤  x ^ 2 * ((1 / log x) * (S + m / (log x - 1) ^ 6)) :=
    mul_le_mul_of_nonneg_left hcore (sq_nonneg x)
  grind

/-- The lower bound, split on the sign of `m`. **The split is the erratum.** -/
theorem ex_pi_gt (m xₐ : ℝ) (hxₐ : 1 < xₐ)
    (hlower : ∀ x > xₐ, x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
      + (m * x / log x ^ 6) < primeCounting x) :
    ∀ x > exp 1 * xₐ,
      exp 1 * x / log x * primeCounting (x / exp 1) >
        x ^ 2 * (1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5
          + 65 / log x ^ 6 + εLower m xₐ x / log x ^ 7) := by
  by_cases hm : 0  ≤  m
  · intro x hx
    simpa [εLower, hm] using ex_pi_gt_nonneg m xₐ hm hlower x hx
  · intro x hx
    simpa [εLower, hm] using ex_pi_gt_neg m xₐ (le_of_not_ge hm) hxₐ hlower x hx

end RamanujanPV.RepairedBounds

-- Exact mathematical source copy, namespace-only adaptation: Solutions/RamanujanNumerics.v1/ForwardRamanujan/Math.lean
/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

namespace RamanujanPV.Budget
open Real IEANTN DudekPlatt.v3

noncomputable def terms (m M A Y : ℝ) : List ℝ :=
  [2*M,(2*M+132)/Y,(4*M+288)/Y^2,(12*M+576)/Y^3,
    48*M/Y^4,M^2/Y^5,max 0 (-m)*(1+1/A)^6]

noncomputable def upper (m M A Y : ℝ) : ℝ :=
  (terms m M A Y).sum-134-max 0 m

/-- The existing two-sided analytic input, kept separate from numerical soundness. -/
def PiInput (m M A : ℝ) : Prop :=
  (∀ x > exp A,mainTerm x+m*x/log x^6 < primeCounting x) ∧
  (∀ x > exp (A+1),primeCounting x < mainTerm x+M*x/log x^6)

noncomputable def gap (x : ℝ) : ℝ :=
  exp 1*x/log x*primeCounting (x/exp 1)-primeCounting x^2
noncomputable def loss (x : ℝ) : ℝ := max 0 (1-log x^6/x^2*gap x)

/-- Generic endpoint majorant, including the repaired negative-lower-coefficient case. -/
theorem epsilon_majorant {m M A Y x : ℝ} (hM : 0  ≤  M) (hY : 0<Y)
    (hx : Y  ≤  log x) : εUpper M x-εLower m (exp A) x  ≤  upper m M A Y := by
  have hL : 0<log x := hY.trans_le hx
  have key (c : ℝ) (k : ℕ) (hc : 0 ≤ c) : c/log x^k  ≤  c/Y^k :=
    div_le_div_of_nonneg_left hc (by positivity) (pow_le_pow_left₀ hY.le hx k)
  have h1 : (2*M+132)/log x  ≤  (2*M+132)/Y := by simpa using key _ 1 (by linarith)
  have h2 := key (4*M+288) 2 (by linarith)
  have h3 := key (12*M+576) 3 (by linarith)
  have h4 := key (48*M) 4 (by positivity)
  have h5 := key (M^2) 5 (sq_nonneg M)
  have n1 : (0:ℝ) ≤ 364/log x := by positivity
  have n2 : (0:ℝ) ≤ 381/log x^2 := by positivity
  have n3 : (0:ℝ) ≤ 238/log x^3 := by positivity
  have n4 : (0:ℝ) ≤ 97/log x^4 := by positivity
  have n5 : (0:ℝ) ≤ 30/log x^5 := by positivity
  have n6 : (0:ℝ) ≤ 8/log x^6 := by positivity
  have hlo : 206+max 0 m-max 0 (-m)*(1+1/A)^6  ≤  εLower m (exp A) x := by
    by_cases hm : 0 ≤ m
    · rw [εLower,if_pos hm,εPos,max_eq_right hm,max_eq_left (by linarith : -m ≤ 0)]
      nlinarith
    · have hm0 : m ≤ 0 := (lt_of_not_ge hm).le
      rw [εLower,if_neg hm,εNeg,log_exp,max_eq_left hm0,max_eq_right (by linarith : 0 ≤ -m)]
      nlinarith
  simp only [upper,terms,List.sum_cons,List.sum_nil,add_zero,εUpper]
  linarith

/-- Quantitative content of the original repaired Ramanujan proof. -/
theorem gap_from_budget {m M A Y C x : ℝ} (hA : 0<A) (hAY : A+1 ≤ Y)
    (hpi : PiInput m M A) (hx : exp Y<x)
    (hbudget : εUpper M x-εLower m (exp A) x  ≤  C) :
    x^2*((log x-C)/log x^7)<gap x := by
  have hxe : exp 1*exp A<x := by
    rw [←exp_add]
    exact (exp_le_exp.mpr (by linarith : (1:ℝ)+A ≤ Y)).trans_lt hx
  have hxa : 1<exp A := by simpa using exp_lt_exp.mpr hA
  have hxx : exp A<x := (exp_lt_exp.mpr (by linarith : A<Y)).trans hx
  have hxxUpper : exp (A+1)<x := (exp_le_exp.mpr hAY).trans_lt hx
  have hsq := RamanujanPV.RepairedBounds.sq_pi_lt M (exp (A+1))
    (fun t ht => by simpa only [mainTerm] using hpi.2 t ht) x hxxUpper
  have hlo := RamanujanPV.RepairedBounds.ex_pi_gt m (exp A) hxa
    (fun t ht => by simpa only [mainTerm] using hpi.1 t ht) x hxe
  have hL : 0<log x := by
    have hy := log_lt_log (exp_pos Y) hx
    rw [log_exp] at hy
    linarith
  have hx0 : 0<x := (exp_pos Y).trans hx
  have hid :
      (1/log x^2+2/log x^3+5/log x^4+16/log x^5+65/log x^6+
        εLower m (exp A) x/log x^7)-
      (1/log x^2+2/log x^3+5/log x^4+16/log x^5+64/log x^6+
        εUpper M x/log x^7) = (log x-(εUpper M x-εLower m (exp A) x))/log x^7 := by
    field_simp [hL.ne'];ring
  have hgap : x^2*((log x-(εUpper M x-εLower m (exp A) x))/log x^7)<gap x := by
    rw [←hid]
    unfold gap
    nlinarith
  have hquot : (log x-C)/log x^7  ≤ 
      (log x-(εUpper M x-εLower m (exp A) x))/log x^7 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  exact (mul_le_mul_of_nonneg_left hquot (sq_nonneg x)).trans_lt hgap

/-- The output certificate becomes a bound on the actual pi-expression, not merely on a parameter. -/
theorem loss_from_budget {m M A Y C x : ℝ} (hA : 0<A) (hAY : A+1 ≤ Y)
    (hpi : PiInput m M A) (hC : 0 ≤ C) (hx : exp Y<x)
    (hbudget : εUpper M x-εLower m (exp A) x  ≤  C) : loss x  ≤  C/log x := by
  have hg := gap_from_budget hA hAY hpi hx hbudget
  have hx0 : 0<x := (exp_pos Y).trans hx
  have hL : 0<log x := by
    have hy := log_lt_log (exp_pos Y) hx
    rw [log_exp] at hy
    linarith
  have hn := mul_lt_mul_of_pos_left hg (show (0:ℝ)<log x^6/x^2 by positivity)
  have hid : log x^6/x^2*(x^2*((log x-C)/log x^7))=1-C/log x := by
    field_simp [hL.ne',hx0.ne']
  rw [hid] at hn
  exact max_le (by positivity) (by linarith)

end RamanujanPV.Budget
namespace RamanujanPV.QuantitativeTail
open Real IEANTN DudekPlatt.v3

/-- The retained positive lower-coefficient case allows exact cancellation of four terms.
This certificate uses kernel rational arithmetic only. -/
theorem budget137 {x : ℝ} (hL : 168  ≤  log x) :
    εUpper 170 x - εLower 70 (exp 144) x < 137 := by
  have hl : 0 < log x := by linarith
  have h1 : (108 : ℝ) / log x  ≤  108 / 168 := by gcongr
  have h2 : (587 : ℝ) / log x ^ 2  ≤  587 / 168 ^ 2 := by gcongr
  have h3 : (2378 : ℝ) / log x ^ 3  ≤  2378 / 168 ^ 3 := by gcongr
  have h4 : (8063 : ℝ) / log x ^ 4  ≤  8063 / 168 ^ 4 := by gcongr
  have h5 : (28870 : ℝ) / log x ^ 5  ≤  28870 / 168 ^ 5 := by gcongr
  have hn : 0  ≤  (8 : ℝ) / log x ^ 6 := by positivity
  have hid : εUpper 170 x - εLower 70 (exp 144) x =
      136 + 108 / log x + 587 / log x ^ 2 + 2378 / log x ^ 3 +
      8063 / log x ^ 4 + 28870 / log x ^ 5 - 8 / log x ^ 6 := by
    norm_num [εUpper, εLower, εPos]
    ring
  rw [hid]
  norm_num at h1 h2 h3 h4 h5
  linarith

/-- A closed quantitative ray for actual prime counting. The only mathematical premise is
exactly the existing IEANTN Phase2 two-sided pi conclusion, not Ramanujan positivity. -/
theorem gap_gt_37_200
    (hpi : DudekPlattNumerics.v6.pi_two_sided_144)
    {x : ℝ} (hx : exp 169  ≤  x) :
    (37 / 200 : ℝ) * x ^ 2 / log x ^ 6 < RamanujanPV.gap x := by
  have hx0 : 0 < x := (exp_pos 169).trans_le hx
  have hL : 169  ≤  log x := by simpa using log_le_log (exp_pos 169) hx
  have hl : 0 < log x := by linarith
  have h168 : exp 168 < x :=
    (exp_lt_exp.mpr (by norm_num : (168 : ℝ) < 169)).trans_le hx
  have hinput : RamanujanPV.Budget.PiInput 70 170 144 := by
    constructor
    · intro t ht
      exact (hpi t ht).1
    · intro t ht
      exact (hpi t ((exp_lt_exp.mpr (by norm_num : (144 : ℝ) < 144 + 1)).trans ht)).2
  have hg := RamanujanPV.Budget.gap_from_budget
    (by norm_num : (0 : ℝ) < 144) (by norm_num : (144 : ℝ) + 1  ≤  168)
    hinput h168 (budget137 (by linarith : 168  ≤  log x)).le
  have hn : (37 / 200 : ℝ) * log x  ≤  log x - 137 := by linarith
  have hquot := div_le_div_of_nonneg_right hn (pow_pos hl 7).le
  have hmul := mul_le_mul_of_nonneg_left hquot (sq_nonneg x)
  have hid : (37 / 200 : ℝ) * x ^ 2 / log x ^ 6 =
      x ^ 2 * (((37 / 200 : ℝ) * log x) / log x ^ 7) := by
    field_simp [hl.ne'] <;> ring
  rw [hid]
  exact hmul.trans_lt hg

theorem holds_of_pi_two_sided_144
    (hpi : DudekPlattNumerics.v6.pi_two_sided_144) {x : ℝ} (hx : exp 169  ≤  x) :
    RamanujanPV.Holds x := by
  have hl : 0 < log x := by
    have : (169 : ℝ)  ≤  log x := by simpa using log_le_log (exp_pos 169) hx
    linarith
  have hx0 : 0 < x := (exp_pos 169).trans_le hx
  apply (RamanujanPV.holds_iff_gap_pos x).2
  exact (show (0 : ℝ) < (37 / 200 : ℝ) * x ^ 2 / log x ^ 6 by positivity).trans
    (gap_gt_37_200 hpi hx)

#print axioms budget137
#print axioms gap_gt_37_200
#print axioms holds_of_pi_two_sided_144
end RamanujanPV.QuantitativeTail

namespace RamanujanPV.Middle
open Real IEANTN MeasureTheory

/-- Signed errors of the actual functions, rather than independent surrogates. -/
noncomputable def thetaErrorLog (L : ℝ) : ℝ := exp (-L) * Chebyshev.theta (exp L) - 1
noncomputable def piErrorLog (L : ℝ) : ℝ :=
  L * exp (-L) * (primeCounting (exp L) - IEANTN.li (exp L))

/-- Exact partial summation at a=40. Its proof for the project's principal-value li is an
explicit remaining analytic obligation. Passing it as an argument does not close that task. -/
def PartialSummation40 : Prop := ∀ L : ℝ, 40 ≤ L →
  piErrorLog L = thetaErrorLog L + (L / 40) * exp (40 - L) *
    (piErrorLog 40 - thetaErrorLog 40) +
    L * exp (-L) * ∫ v in (40 : ℝ)..L, exp v * thetaErrorLog v / v ^ 2

/-- A simple global theta majorant derivable from CH2 Corollary1.3 and the Dusart
psi-minus-theta bound. That source deduction is not silently assumed proved here. -/
def ThetaMajorant40 (b : ℝ) : Prop :=
  ∀ L : ℝ, 40 ≤ L → |thetaErrorLog L| ≤ b + 116 * exp (-L / 2)

/-- The analytic integral is proved from the pointwise majorant; no integral enclosure
or desired Ramanujan comparison is a hypothesis. -/
theorem error_integral_bound {b L : ℝ} (hb : 0 ≤ b) (hL : 40 ≤ L)
    (hθ : ThetaMajorant40 b) :
    |∫ v in (40 : ℝ)..L, exp v * thetaErrorLog v / v ^ 2| ≤
      b / 1600 * exp L + (232 / 1600 : ℝ) * exp (L / 2) := by
  have he : IntervalIntegrable exp volume 40 L := continuous_exp.intervalIntegrable _ _
  have hh : IntervalIntegrable (fun v : ℝ => exp (v / 2)) volume 40 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi : IntervalIntegrable
      (fun v : ℝ => b / 1600 * exp v + (116 / 1600 : ℝ) * exp (v / 2))
      volume 40 L := (he.const_mul _).add (hh.const_mul _)
  have hp : ∀ v ∈ Set.Ioc (40 : ℝ) L,
      ‖exp v * thetaErrorLog v / v ^ 2‖ ≤
        b / 1600 * exp v + (116 / 1600 : ℝ) * exp (v / 2) := by
    intro v hv
    have hv0 : 0 < v := by linarith [hv.1]
    have hv2 : (1600 : ℝ) ≤ v ^ 2 := by nlinarith [hv.1]
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (exp_pos v),
      abs_of_nonneg (sq_nonneg v)]
    calc
      exp v * |thetaErrorLog v| / v ^ 2 ≤
          exp v * (b + 116 * exp (-v / 2)) / v ^ 2 := by
        gcongr
        exact hθ v hv.1.le
      _ ≤ exp v * (b + 116 * exp (-v / 2)) / 1600 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hv2
      _ = _ := by
        have hprod : exp v * exp (-v / 2) = exp (v / 2) := by
          rw [← exp_add]
          congr 1
          ring
        calc
          _ = (b * exp v + 116 * (exp v * exp (-v / 2))) / 1600 := by ring
          _ = _ := by rw [hprod]; ring
  have hi' := intervalIntegral.norm_integral_le_of_norm_le hL
    (Filter.Eventually.of_forall hp) hi
  rw [Real.norm_eq_abs, intervalIntegral.integral_add (he.const_mul _) (hh.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_exp] at hi'
  have hhalf : (∫ v in (40 : ℝ)..L, exp (v / 2)) =
      2 * (exp (L / 2) - exp 20) := by
    norm_num
  rw [hhalf] at hi'
  have hn : 0 ≤ b / 1600 * exp 40 + (232 / 1600 : ℝ) * exp 20 := by positivity
  linarith

noncomputable def piMajorant (b L : ℝ) : ℝ :=
  b + 116 * exp (-L / 2) +
    (L / 40) * exp (40 - L) * ((5 / 1000000000 : ℝ) + b + 116 * exp (-20)) +
    L * exp (-L) * (b / 1600 * exp L + (232 / 1600 : ℝ) * exp (L / 2))

/-- Actual pi error transport from a concrete theta majorant and an independent
Büthe anchor. The partial-summation input is displayed and remains auditable. -/
theorem actual_pi_error_bound {b L : ℝ} (hb : 0 ≤ b) (hL : 40 ≤ L)
    (hθ : ThetaMajorant40 b) (hanchor : |piErrorLog 40| ≤ (5 / 1000000000 : ℝ))
    (hpartial : PartialSummation40) : |piErrorLog L| ≤ piMajorant b L := by
  have hL0 : 0 < L := by linarith
  have hθ40 := hθ 40 le_rfl
  norm_num only [neg_div, show (40 : ℝ) / 2 = 20 by norm_num] at hθ40
  have hbase : |piErrorLog 40 - thetaErrorLog 40| ≤
      (5 / 1000000000 : ℝ) + b + 116 * exp (-20) := by
    exact (abs_sub _ _).trans (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hbase
    (show 0 ≤ L / 40 * exp (40 - L) by positivity)
  have h2 := mul_le_mul_of_nonneg_left (error_integral_bound hb hL hθ)
    (show 0 ≤ L * exp (-L) by positivity)
  have htri := abs_add_le
    (thetaErrorLog L + L / 40 * exp (40 - L) * (piErrorLog 40 - thetaErrorLog 40))
    (L * exp (-L) * ∫ v in (40 : ℝ)..L, exp v * thetaErrorLog v / v ^ 2)
  have htri' := abs_add_le (thetaErrorLog L)
    (L / 40 * exp (40 - L) * (piErrorLog 40 - thetaErrorLog 40))
  rw [← hpartial L hL] at htri
  rw [abs_mul, abs_of_nonneg (show 0 ≤ L * exp (-L) by positivity)] at htri
  rw [abs_mul, abs_of_nonneg (show 0 ≤ L / 40 * exp (40 - L) by positivity)] at htri'
  unfold piMajorant
  linarith [hθ L hL]

#print axioms error_integral_bound
#print axioms actual_pi_error_bound
end RamanujanPV.Middle

namespace RamanujanPV.Middle
open Real IEANTN

/-- The explicit unweighted CH2 Corollary1.3 contract after safely enlarging its
constant pi/(3*10^12) to b. This is a genuine literature analytic input. -/
def CH2PsiInput (b : ℝ) : Prop := ∀ x : ℝ, 1 ≤ x →
  |Chebyshev.psi x - x| ≤ b * x + (113.67 : ℝ) * sqrt x

/-- Dusart2018 Corollary4.5, in the restricted x>=1 domain needed here.
No numerical prime table or Ramanujan conclusion is included in this input. -/
def DusartPowerInput : Prop := ∀ x : ℝ, 1 ≤ x →
  Chebyshev.psi x - Chebyshev.theta x ≤
    (1.000000147 : ℝ) * sqrt x + (1.78 : ℝ) * x ^ (1 / 3 : ℝ)

/-- A new, fully formal deduction of the simple theta envelope from its two named
source contracts. No numerical exponential evaluation is needed. -/
theorem theta_majorant_of_CH2_Dusart {b : ℝ} (hpsi : CH2PsiInput b)
    (hpower : DusartPowerInput) : ThetaMajorant40 b := by
  intro L hL
  have hL0 : 0 < L := by linarith
  have hx : (1 : ℝ) ≤ exp L := by
    simpa only [exp_zero] using exp_le_exp.mpr hL0.le
  have hp := hpsi (exp L) hx
  have hd := hpower (exp L) hx
  have hthird : (exp L) ^ (1 / 3 : ℝ) = exp (L / 3) := by
    rw [rpow_def_of_pos (exp_pos L), log_exp]
    congr 1
    ring
  rw [← exp_half] at hp
  rw [← exp_half, hthird] at hd
  have he6 : (2 : ℝ) ≤ exp (L / 6) := by
    linarith [add_one_le_exp (L / 6)]
  have heprod : exp (L / 3) * exp (L / 6) = exp (L / 2) := by
    rw [← exp_add]
    congr 1
    ring
  have hthird' : exp (L / 3) ≤ exp (L / 2) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left he6 (exp_pos (L / 3)).le]
  have htri := abs_sub_le (Chebyshev.theta (exp L)) (Chebyshev.psi (exp L)) (exp L)
  rw [abs_sub_comm (Chebyshev.theta (exp L)) (Chebyshev.psi (exp L)),
    abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi (exp L)))] at htri
  have hraw : |Chebyshev.theta (exp L) - exp L| ≤ b * exp L + 116 * exp (L / 2) := by
    nlinarith [exp_pos (L / 2)]
  have hexp : exp (-L) * exp L = 1 := by rw [← exp_add]; simp
  have hnorm : thetaErrorLog L = exp (-L) * (Chebyshev.theta (exp L) - exp L) := by
    unfold thetaErrorLog
    nlinarith
  have hehalf : exp (-L) * exp (L / 2) = exp (-L / 2) := by
    rw [← exp_add]
    congr 1
    ring
  rw [hnorm, abs_mul, abs_of_pos (exp_pos (-L))]
  calc
    exp (-L) * |Chebyshev.theta (exp L) - exp L| ≤
        exp (-L) * (b * exp L + 116 * exp (L / 2)) :=
      mul_le_mul_of_nonneg_left hraw (exp_pos (-L)).le
    _ = b + 116 * exp (-L / 2) := by
      calc
        _ = b * (exp (-L) * exp L) + 116 * (exp (-L) * exp (L / 2)) := by ring
        _ = _ := by rw [hexp, hehalf]; ring

#print axioms theta_majorant_of_CH2_Dusart
end RamanujanPV.Middle

-- Rebuilt mathematical source: Solutions/FKS2.v2/Stieltjes.lean, through piMinusLi_sub.
/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# Partial summation: `π − Li` in terms of `θ`

The paper's (Stieltjes), and the decomposition of `Eπ` that Theorem 3 estimates term by term.

`Mathlib` supplies the harder half — `Chebyshev.primeCounting_eq_theta_div_log_add_integral` is
Abel summation for `π` against `θ`. What is added here is the matching identity for the logarithmic
integral,

`Li(x) = x/log x − 2/log 2 + ∫₂ˣ dt/log²t`,

which is one integration by parts, and then the subtraction that makes the two `∫ dt/log²t` terms
cancel into a single `∫ (θ(t) − t)/(t log²t)`. That is exactly the integral `Integral.lean` bounds.

## What comes out

`piMinusLi_eq` is the identity based at `2`; `piMinusLi_sub` rebases it at any `x₀ ≥ 2`, which is
the form the paper uses so that `π(x₀)` and `θ(x₀)` can be computed numerically. `Epi_le` then
divides through by `x/log x` and applies the triangle inequality, leaving the three terms Theorem 3
bounds separately: a boundary constant, `Eθ(x)` itself, and the integral.
-/

namespace RamanujanPV.ActualPartialSummation

open Real IEANTN intervalIntegral MeasureTheory

theorem continuousOn_inv_log {x : ℝ} (hx : 2 ≤ x) (n : ℕ) :
    ContinuousOn (fun t : ℝ => 1 / (log t) ^ n) (Set.uIcc 2 x) := by
  rw [Set.uIcc_of_le hx]
  intro t ht
  have ht1 : (1 : ℝ) < t := by linarith [ht.1]
  have hlog : 0 < log t := log_pos ht1
  have hne : (log t) ^ n ≠ 0 := pow_ne_zero _ hlog.ne'
  exact ((continuousAt_const.div ((continuousAt_log (by linarith)).pow n) hne)).continuousWithinAt

/-- `Li(x) = x/log x - 2/log 2 + ∫₂ˣ dt/log²t`, by parts. -/
theorem Li_eq {x : ℝ} (hx : 2 ≤ x) :
    Li x = x / log x - 2 / log 2 + ∫ t in (2 : ℝ)..x, 1 / (log t) ^ 2 := by
  have hint1 : IntervalIntegrable (fun t : ℝ => 1 / (log t) ^ 1) volume 2 x :=
    (continuousOn_inv_log hx 1).intervalIntegrable
  have hint2 : IntervalIntegrable (fun t : ℝ => 1 / (log t) ^ 2) volume 2 x :=
    (continuousOn_inv_log hx 2).intervalIntegrable
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun s : ℝ => s / log s) (1 / (log t) ^ 1 - 1 / (log t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have htpos : (0 : ℝ) < t := by linarith [ht.1]
    have hlog : 0 < log t := log_pos (by linarith [ht.1])
    have hL : HasDerivAt log (1 / t) t := by simpa using Real.hasDerivAt_log htpos.ne'
    have hne : log t ≠ 0 := hlog.ne'
    have htne : t ≠ 0 := htpos.ne'
    have h := (hasDerivAt_id t).div hL hne
    refine h.congr_deriv ?_
    simp only [id_eq]
    field_simp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.sub hint2)
  have hsplit := intervalIntegral.integral_sub hint1 hint2
  unfold Li
  simp only [pow_one] at hFTC hsplit hint1 ⊢
  linarith [hFTC, hsplit]


theorem contOn_inv_t_log_sq {x₀ x : ℝ} (hx₀ : 1 < x₀) (hx : x₀ ≤ x) :
    ContinuousOn (fun t : ℝ => (t * (log t) ^ 2)⁻¹) (Set.uIcc x₀ x) := by
  rw [Set.uIcc_of_le hx]
  intro t ht
  have ht1 : 1 < t := lt_of_lt_of_le hx₀ ht.1
  have hlog : 0 < log t := log_pos ht1
  have hne : t * (log t) ^ 2 ≠ 0 := by positivity
  exact ((continuousAt_id.mul
    ((continuousAt_log (by linarith)).pow 2)).inv₀ hne).continuousWithinAt

theorem intervalIntegrable_theta_div {x₀ x : ℝ} (hx₀ : 1 < x₀) (hx : x₀ ≤ x) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * (log t) ^ 2)) volume x₀ x := by
  simpa [div_eq_mul_inv] using
    Chebyshev.theta_mono.intervalIntegrable.mul_continuousOn (contOn_inv_t_log_sq hx₀ hx)

theorem intervalIntegrable_sub_div {x₀ x : ℝ} (hx₀ : 1 < x₀) (hx : x₀ ≤ x) :
    IntervalIntegrable (fun t : ℝ => (Chebyshev.theta t - t) / (t * (log t) ^ 2)) volume x₀ x := by
  have h := (Chebyshev.theta_mono.intervalIntegrable.sub
    (continuous_id.intervalIntegrable (μ := volume) x₀ x)).mul_continuousOn (contOn_inv_t_log_sq hx₀ hx)
  simpa [div_eq_mul_inv] using h

/-- **The Stieltjes identity**: `π(x) − Li(x)` in terms of `θ`. -/
theorem piMinusLi_eq {x : ℝ} (hx : 2 ≤ x) :
    primeCounting x - Li x
      = (Chebyshev.theta x - x) / log x + 2 / log 2
        + ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2) := by
  have hpi := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
  have hli := Li_eq hx
  have hint2 : IntervalIntegrable (fun t : ℝ => 1 / (log t) ^ 2) volume 2 x :=
    (continuousOn_inv_log hx 2).intervalIntegrable
  have hcongr : (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2))
      = (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * (log t) ^ 2))
        - ∫ t in (2 : ℝ)..x, 1 / (log t) ^ 2 := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_theta_div one_lt_two hx) hint2]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx] at ht
    have htne : t ≠ 0 := by linarith [ht.1]
    have hlog : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    field_simp
  unfold primeCounting Li
  rw [hcongr, sub_div]
  unfold Li at hli
  rw [hpi]
  linarith [hli]


/-- The Stieltjes identity relative to a base point `x₀`, the paper's displayed rewrite. -/
theorem piMinusLi_sub {x₀ x : ℝ} (hx₀ : 2 ≤ x₀) (hx : x₀ ≤ x) :
    primeCounting x - Li x
      = (primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀)
        + (Chebyshev.theta x - x) / log x
        + ∫ t in x₀..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2) := by
  have hx2 : (2 : ℝ) ≤ x := le_trans hx₀ hx
  have h1 := piMinusLi_eq hx2
  have h2 := piMinusLi_eq hx₀
  have hsplit := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_sub_div one_lt_two hx2) (intervalIntegrable_sub_div one_lt_two hx₀)
  linarith

end RamanujanPV.ActualPartialSummation

namespace RamanujanPV.Middle
open Real IEANTN MeasureTheory

/-- The standard principal-value/offset logarithmic integral identity. The project
Vocabulary defines these independently, so the identity remains a clearly named
unformalized analytic input; unlike PartialSummation40 it involves no primes. -/
def LiOffsetIdentity : Prop := ∀ x : ℝ, 2 ≤ x → IEANTN.li x = IEANTN.Li x + IEANTN.li 2

/-- Rebased partial summation for actual pi, reduced to the no-primes li identity. -/
theorem actual_partial_summation {a x : ℝ} (ha : 2 ≤ a) (hax : a ≤ x)
    (hoffset : LiOffsetIdentity) :
    primeCounting x - IEANTN.li x =
      (primeCounting a - IEANTN.li a - (Chebyshev.theta a - a) / log a) +
      (Chebyshev.theta x - x) / log x +
      ∫ t in a..x, (Chebyshev.theta t - t) / (t * log t ^ 2) := by
  have h := RamanujanPV.ActualPartialSummation.piMinusLi_sub ha hax
  rw [hoffset a ha, hoffset x (ha.trans hax)]
  linarith

/-- Logarithmic change of variables is proved for the genuine discontinuous theta
integrand using the monotone C1 substitution theorem; no continuity at prime jumps
is assumed. -/
theorem actual_error_integral_log_substitution {L : ℝ} (hL : 40 ≤ L) :
    (∫ t in exp (40 : ℝ)..exp L, (Chebyshev.theta t - t) / (t * log t ^ 2)) =
      ∫ v in (40 : ℝ)..L, exp v * thetaErrorLog v / v ^ 2 := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := exp) (f' := exp)
    (g := fun t : ℝ => (Chebyshev.theta t - t) / (t * log t ^ 2))
    (a := (40 : ℝ)) (b := L) continuous_exp.continuousOn
    (fun v _ => hasDerivAt_exp v) (fun v _ => (exp_pos v).le)
  rw [← h]
  apply intervalIntegral.integral_congr
  intro v hv
  have hv0 : 0 < v := by
    rw [Set.uIcc_of_le hL] at hv
    linarith [hv.1]
  dsimp [Function.comp_def, thetaErrorLog]
  rw [log_exp, exp_neg]
  field_simp [(exp_pos v).ne', hv0.ne']
  <;> ring

/-- All actual-prime partial-summation and exponential-substitution obligations are
closed here. Only the independent principal-value li normalization is conditional. -/
theorem partial_summation40_of_li_offset (hoffset : LiOffsetIdentity) : PartialSummation40 := by
  intro L hL
  have hL0 : 0 < L := by linarith
  have ha : (2 : ℝ) ≤ exp 40 := by linarith [add_one_le_exp (40 : ℝ)]
  have hbase := actual_partial_summation ha (exp_le_exp.mpr hL) hoffset
  rw [actual_error_integral_log_substitution hL, log_exp, log_exp] at hbase
  unfold piErrorLog
  rw [hbase]
  dsimp [thetaErrorLog]
  rw [exp_sub, exp_neg, exp_neg]
  field_simp [(exp_pos L).ne', (exp_pos (40 : ℝ)).ne', hL0.ne']
  <;> ring

/-- Combined actual-pi consequence with only named source analytic premises:
CH2, Dusart, a Büthe point enclosure, and the prime-free li normalization. -/
theorem pi_error_from_CH2_Dusart_Buthe {b L : ℝ} (hb : 0 ≤ b) (hL : 40 ≤ L)
    (hpsi : CH2PsiInput b) (hpower : DusartPowerInput)
    (hanchor : |piErrorLog 40| ≤ (5 / 1000000000 : ℝ))
    (hoffset : LiOffsetIdentity) : |piErrorLog L| ≤ piMajorant b L :=
  actual_pi_error_bound hb hL (theta_majorant_of_CH2_Dusart hpsi hpower) hanchor
    (partial_summation40_of_li_offset hoffset)

#print axioms actual_partial_summation
#print axioms actual_error_integral_log_substitution
#print axioms partial_summation40_of_li_offset
#print axioms pi_error_from_CH2_Dusart_Buthe
end RamanujanPV.Middle

namespace RamanujanPV.Middle
open Real IEANTN MeasureTheory

/-- Büthe's signed theta information is stronger than the old scalar pi upper
input: keeping the pointwise deficit recovers a useful sqrt(x)/log(x) term. -/
theorem pi_upper_from_theta_deficit {x α : ℝ} (hx : 2 ≤ x) (hα : 0 ≤ α)
    (hθ : ∀ t : ℝ, 2 ≤ t → t ≤ x → Chebyshev.theta t - t ≤ -α * sqrt t)
    (hoffset : LiOffsetIdentity) (hli2 : 0 ≤ IEANTN.li 2)
    (hlog2 : (2 / 3 : ℝ) ≤ log 2) :
    primeCounting x ≤ IEANTN.li x + 3 - α * sqrt x / log x := by
  have hl2 : 0 < log (2 : ℝ) := by linarith
  have hlx : 0 < log x := log_pos (by linarith)
  have hconst : (2 : ℝ) / log 2 ≤ 3 := (div_le_iff₀ hl2).2 (by linarith)
  have hnonneg : 0 ≤ ∫ t in (2 : ℝ)..x,
      -((Chebyshev.theta t - t) / (t * log t ^ 2)) := by
    apply intervalIntegral.integral_nonneg hx
    intro t ht
    have hθt := hθ t ht.1 ht.2
    have hnum : Chebyshev.theta t - t ≤ 0 := by
      have : 0 ≤ α * sqrt t := by positivity
      linarith
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hden : 0 ≤ t * log t ^ 2 := by positivity
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hnum hden)
  rw [intervalIntegral.integral_neg] at hnonneg
  have hp := RamanujanPV.ActualPartialSummation.piMinusLi_eq hx
  have hpoint := div_le_div_of_nonneg_right (hθ x hx le_rfl) hlx.le
  have hneg : -α * sqrt x / log x = -(α * sqrt x / log x) := by ring
  rw [hneg] at hpoint
  rw [hoffset x hx]
  linarith only [hp, hpoint, hconst, hnonneg, hli2]

#print axioms pi_upper_from_theta_deficit
end RamanujanPV.Middle

-- Rebuilt mathematical source: Solutions/DudekPlattNumerics.v4/ThetaPi.lean
/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastián Rodrigo (AI-assisted)
-/

/-!
# Native theta-to-pi partial summation and finite integration by parts

These are helper theorems, not graph inputs. The first identity uses Mathlib's
Abel summation theorem for the actual prime counting function (including jumps
and natural-floor endpoint conventions). No hypothesis about primes is used.
-/

namespace RamanujanPV.LogCalculus

open Real MeasureTheory Set

noncomputable def thetaError (t : ℝ) : ℝ := Chebyshev.theta t - t
noncomputable def logIntegral (k : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ k
noncomputable def errorIntegral (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, thetaError t / (t * Real.log t ^ 2)
noncomputable def S5 (x : ℝ) : ℝ :=
  x * ∑ k ∈ Finset.range 5, (Nat.factorial k : ℝ) / Real.log x ^ (k + 1)
noncomputable def A : ℝ :=
  1 / log 2 ^ 2 + 2 / log 2 ^ 3 + 6 / log 2 ^ 4 +
    24 / log 2 ^ 5 + 120 / log 2 ^ 6

/-- The expanded lower-end constant is exactly the factorial sum in the paper. -/
lemma A_eq_sum : A = ∑ k ∈ Finset.range 5,
    (Nat.factorial (k + 1) : ℝ) / log 2 ^ (k + 2) := by
  norm_num [A, Finset.sum_range_succ, Nat.factorial]

lemma intervalIntegrable_logKernel (k : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ ↦ 1 / log t ^ k) volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.mem_uIcc] at ht
  have ht1 : 1 < t := by rcases ht with ht | ht <;> linarith [ht.1, ht.2]
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl : log t ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt (log_pos ht1))
  fun_prop

lemma intervalIntegrable_thetaKernel {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ Chebyshev.theta t / (t * log t ^ 2)) volume a b := by
  apply intervalIntegrable_iff.mpr
  apply (Chebyshev.integrableOn_theta_div_id_mul_log_sq (max a b)).mono_set
  intro t ht
  exact ⟨le_trans (le_min ha hb) ht.1.le, ht.2⟩

lemma intervalIntegrable_errorKernel {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ thetaError t / (t * log t ^ 2)) volume a b := by
  have hi := (intervalIntegrable_thetaKernel ha hb).sub
    (intervalIntegrable_logKernel 2 (by linarith : 1 < a) (by linarith : 1 < b))
  apply hi.congr
  intro t ht
  have ht0 : t ≠ 0 := by
    have := lt_of_le_of_lt (le_min ha hb) ht.1
    linarith
  dsimp [thetaError]
  field_simp

/-- Native Abel summation after separating the elementary part of theta. -/
theorem primeCounting_eq_error {x : ℝ} (hx : 2 ≤ x) :
    IEANTN.primeCounting x = x / log x + logIntegral 2 x +
      thetaError x / log x + errorIntegral x := by
  have hs := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
  have hi := intervalIntegral.integral_sub
    (intervalIntegrable_thetaKernel (le_refl 2) hx)
    (intervalIntegrable_logKernel 2 (by norm_num : (1 : ℝ) < 2) (by linarith : 1 < x))
  have he : errorIntegral x =
      (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * log t ^ 2)) - logIntegral 2 x := by
    rw [errorIntegral, logIntegral, ← hi]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : t ≠ 0 := by rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
    dsimp [thetaError]
    field_simp
  dsimp [IEANTN.primeCounting]
  rw [he, hs]
  dsimp [thetaError]
  ring

lemma hasDerivAt_div_log_pow (k : ℕ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ ↦ t / log t ^ (k + 1))
      (1 / log t ^ (k + 1) - (k + 1 : ℝ) / log t ^ (k + 2)) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl : log t ≠ 0 := ne_of_gt (log_pos ht)
  convert! (hasDerivAt_id t).div ((hasDerivAt_log ht0).pow (k + 1))
    (pow_ne_zero _ hl) using 1
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq, pow_zero, one_mul]
  field_simp

/-- Integration by parts with the actual lower endpoint 2. -/
theorem logIntegral_recurrence (k : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    logIntegral (k + 1) x = x / log x ^ (k + 1) - 2 / log 2 ^ (k + 1) +
      (k + 1 : ℝ) * logIntegral (k + 2) x := by
  have h1 : 1 < x := by linarith
  have hi1 := intervalIntegrable_logKernel (k + 1) (by norm_num : (1 : ℝ) < 2) h1
  have hi2 := (intervalIntegrable_logKernel (k + 2)
    (by norm_num : (1 : ℝ) < 2) h1).const_mul (k + 1 : ℝ)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (2 : ℝ)) (b := x)
    (f := fun t : ℝ ↦ t / log t ^ (k + 1))
    (f' := fun t : ℝ ↦ 1 / log t ^ (k + 1) - (k + 1 : ℝ) / log t ^ (k + 2))
    (fun t ht ↦ hasDerivAt_div_log_pow k (by
      rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]))
    (by simpa only [div_eq_mul_inv, one_mul] using hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 (by
    simpa only [div_eq_mul_inv, one_mul] using hi2)] at hf
  simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul] at hf
  dsimp [logIntegral]
  simp only [div_eq_mul_inv, one_mul] at hf ⊢
  linarith

/-- Five finite integrations by parts. There is no primewise differentiation. -/
theorem mainTerm_identity {x : ℝ} (hx : 2 ≤ x) :
    x / log x + logIntegral 2 x =
      S5 x + 120 * x / log x ^ 6 + 720 * logIntegral 7 x - 2 * A := by
  have h2 := logIntegral_recurrence 1 hx
  have h3 := logIntegral_recurrence 2 hx
  have h4 := logIntegral_recurrence 3 hx
  have h5 := logIntegral_recurrence 4 hx
  have h6 := logIntegral_recurrence 5 hx
  norm_num at h2 h3 h4 h5 h6
  rw [h2, h3, h4, h5, h6]
  dsimp [S5, A]
  norm_num [Finset.sum_range_succ, Nat.factorial]
  ring

/-- Exact identity required for the Dudek--Platt numerical derivation. -/
theorem primeCounting_expansion {x : ℝ} (hx : 2 ≤ x) :
    IEANTN.primeCounting x = S5 x + 120 * x / log x ^ 6 +
      720 * logIntegral 7 x - 2 * A + thetaError x / log x + errorIntegral x := by
  rw [primeCounting_eq_error hx, mainTerm_identity hx]

end RamanujanPV.LogCalculus

namespace RamanujanPV.LiBarriers
open Real IEANTN MeasureTheory
open RamanujanPV.Middle
open RamanujanPV.LogCalculus (logIntegral intervalIntegrable_logKernel logIntegral_recurrence)

noncomputable def F10 (x : ℝ) : ℝ :=
  x * ∑ k ∈ Finset.range 10, (Nat.factorial k : ℝ) / log x ^ (k + 1)

/-- Ten exact integrations by parts, with the original lower endpoint2 retained. -/
theorem Li_ten_parts {x : ℝ} (hx : 2 ≤ x) :
    IEANTN.Li x = F10 x - F10 2 + (Nat.factorial 10 : ℝ) * logIntegral 11 x := by
  have h0 := logIntegral_recurrence 0 hx
  have h1 := logIntegral_recurrence 1 hx
  have h2 := logIntegral_recurrence 2 hx
  have h3 := logIntegral_recurrence 3 hx
  have h4 := logIntegral_recurrence 4 hx
  have h5 := logIntegral_recurrence 5 hx
  have h6 := logIntegral_recurrence 6 hx
  have h7 := logIntegral_recurrence 7 hx
  have h8 := logIntegral_recurrence 8 hx
  have h9 := logIntegral_recurrence 9 hx
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have heq : IEANTN.Li x = logIntegral 1 x := by simp [IEANTN.Li, logIntegral]
  rw [heq]
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  norm_num [F10, Finset.sum_range_succ, Nat.factorial]
  <;> ring

theorem F10_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ F10 x := by
  have hl : 0 < log x := log_pos hx
  unfold F10
  apply mul_nonneg (by linarith)
  apply Finset.sum_nonneg
  intro k hk
  positivity

theorem F10_two_bound (hlog2 : (2 / 3 : ℝ) ≤ log 2) : F10 2 ≤ 100000000 := by
  have hl : 0 < log (2 : ℝ) := by linarith
  have hsum : (∑ k ∈ Finset.range 10, (Nat.factorial k : ℝ) / log (2 : ℝ) ^ (k+1)) ≤
      ∑ k ∈ Finset.range 10, (Nat.factorial k : ℝ) / (2 / 3 : ℝ) ^ (k+1) := by
    apply Finset.sum_le_sum
    intro k hk
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by norm_num) hlog2 _
  unfold F10
  have hmul := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hmul
  linarith

/-- The small constant allowance is derived from the actual endpoint terms,
not guessed or supplied as a hardcoded output certificate. -/
theorem actual_li_lower {x : ℝ} (hx : 2 ≤ x)
    (hoffset : LiOffsetIdentity) (hli2 : 0 ≤ IEANTN.li 2)
    (hlog2 : (2 / 3 : ℝ) ≤ log 2) : F10 x - 100000000 ≤ IEANTN.li x := by
  have hi : 0 ≤ logIntegral 11 x := by
    unfold logIntegral
    apply intervalIntegral.integral_nonneg hx
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have hlt : 0 < log t := log_pos ht1
    positivity
  rw [hoffset x hx, Li_ten_parts hx]
  have hf := F10_two_bound hlog2
  have hfi : (0 : ℝ) ≤ (Nat.factorial 10 : ℝ) * logIntegral 11 x := by positivity
  linarith

#print axioms Li_ten_parts
#print axioms F10_two_bound
#print axioms actual_li_lower
end RamanujanPV.LiBarriers

namespace RamanujanPV.LiBarriers
open Real IEANTN MeasureTheory
open RamanujanPV.Middle
open RamanujanPV.LogCalculus (logIntegral intervalIntegrable_logKernel)

/-- Genuine FTC derivative of the offset logarithmic kernels, including all
local-domain and measurability requirements. -/
theorem logIntegral_hasDerivAt (k : ℕ) {x : ℝ} (hx : 2 < x) :
    HasDerivAt (logIntegral k) (1 / log x ^ k) x := by
  have hm : Measurable (fun t : ℝ => 1 / log t ^ k) := by fun_prop
  have hc : ContinuousAt (fun t : ℝ => 1 / log t ^ k) x := by
    have hx0 : x ≠ 0 := by linarith
    have hl : log x ≠ 0 := (log_pos (by linarith : 1 < x)).ne'
    exact continuousAt_const.div ((continuousAt_log hx0).pow k) (pow_ne_zero k hl)
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_logKernel k (by norm_num) (by linarith))
    hm.stronglyMeasurable.stronglyMeasurableAtFilter hc

theorem offset_Li_hasDerivAt {x : ℝ} (hx : 2 < x) :
    HasDerivAt IEANTN.Li (1 / log x) x := by
  have h := logIntegral_hasDerivAt 1 hx
  have heq : logIntegral 1 = IEANTN.Li := by
    funext y
    simp [logIntegral, IEANTN.Li]
  simpa only [heq, pow_one] using h

theorem actual_li_hasDerivAt (hoffset : LiOffsetIdentity) {x : ℝ} (hx : 2 < x) :
    HasDerivAt IEANTN.li (1 / log x) x := by
  have h := (offset_Li_hasDerivAt hx).add_const (IEANTN.li 2)
  apply h.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hx] with t ht
  exact hoffset t ht.le

theorem F10_hasDerivAt {x : ℝ} (hx : 2 < x) :
    HasDerivAt F10 (1 / log x - (Nat.factorial 10 : ℝ) / log x ^ 11) x := by
  have h := ((offset_Li_hasDerivAt hx).add_const (F10 2)).sub
    ((logIntegral_hasDerivAt 11 hx).const_mul (Nat.factorial 10 : ℝ))
  have heq : F10 =ᶠ[nhds x] fun t : ℝ =>
      IEANTN.Li t + F10 2 - (Nat.factorial 10 : ℝ) * logIntegral 11 t := by
    filter_upwards [lt_mem_nhds hx] with t ht
    linarith [Li_ten_parts ht.le]
  simpa only [mul_one_div] using h.congr_of_eventuallyEq heq

/-- A deliberately loose base estimate, sufficient to avoid an extra Ei numerical
certificate when constructing the high-order analytic barrier. -/
theorem li_exp17_upper (hoffset : LiOffsetIdentity) (hli2 : IEANTN.li 2 ≤ 2)
    (hlog2 : (2 / 3 : ℝ) ≤ log 2) : IEANTN.li (exp 17) ≤ 100000000 := by
  have he2 : (2 : ℝ) ≤ exp 17 := by linarith [add_one_le_exp (17 : ℝ)]
  have hi : IntervalIntegrable (fun t : ℝ => 1 / log t) volume 2 (exp 17) := by
    simpa only [pow_one, logIntegral] using
      intervalIntegrable_logKernel 1 (by norm_num) (by linarith : 1 < exp (17 : ℝ))
  have hb := intervalIntegral.integral_mono_on he2 hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (3 / 2 : ℝ)) volume 2 (exp 17))
    (fun t ht => by
      have hl : (2 / 3 : ℝ) ≤ log t := hlog2.trans (log_le_log (by norm_num) ht.1)
      have hl0 : 0 < log t := by linarith
      exact (div_le_iff₀ hl0).2 (by linarith))
  rw [intervalIntegral.integral_const] at hb
  have he1 : exp 1 ≤ (68 / 25 : ℝ) := by linarith [exp_one_lt_d9]
  have he17 : exp (17 : ℝ) ≤ (68 / 25 : ℝ)^17 := by
    have h := pow_le_pow_left₀ (exp_pos 1).le he1 17
    convert! h using 1 <;> norm_num [← exp_nat_mul]
  have heBound : exp (17 : ℝ) ≤ 49000000 := by
    exact he17.trans (by norm_num)
  rw [hoffset (exp 17) he2]
  unfold IEANTN.Li
  norm_num only [smul_eq_mul] at hb
  linarith

/-- The extra 1e8 is an analytically derived endpoint allowance. The variable
correction retains enough factorial terms to preserve cancellation in Ramanujan's gap. -/
theorem actual_li_upper {x : ℝ} (hx : exp 17 ≤ x)
    (hoffset : LiOffsetIdentity) (hli2 : IEANTN.li 2 ≤ 2)
    (hlog2 : (2 / 3 : ℝ) ≤ log 2) :
    IEANTN.li x ≤ F10 x + 3 * (Nat.factorial 10 : ℝ) * x / log x ^ 11 + 100000000 := by
  let f : ℝ → ℝ := fun t => IEANTN.li t - F10 t -
    3 * (Nat.factorial 10 : ℝ) * t / log t ^ 11
  have hd : ∀ t ∈ Set.Ici (exp (17 : ℝ)),
      HasDerivAt f ((Nat.factorial 10 : ℝ) * (33 - 2 * log t) / log t ^ 12) t := by
    intro t ht
    have he2 : (2 : ℝ) < exp 17 := by linarith [add_one_le_exp (17 : ℝ)]
    have ht2 : 2 < t := he2.trans_le ht
    have hln : log t ≠ 0 := (log_pos (by linarith : 1 < t)).ne'
    have h := ((actual_li_hasDerivAt hoffset ht2).sub (F10_hasDerivAt ht2)).sub
      ((RamanujanPV.LogCalculus.hasDerivAt_div_log_pow 10 (by linarith : 1 < t)).const_mul
        (3 * (Nat.factorial 10 : ℝ)))
    have hfun : (IEANTN.li - F10 - fun y : ℝ =>
        3 * (Nat.factorial 10 : ℝ) * (y / log y ^ (10 + 1))) = f := by
      funext y
      dsimp [f]
      ring
    rw [hfun] at h
    apply h.congr_deriv
    norm_num
    field_simp [hln]
    <;> ring
  have hm : AntitoneOn f (Set.Ici (exp (17 : ℝ))) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      have he2 : (0 : ℝ) < t := (exp_pos 17).trans_le (interior_subset ht)
      have hL : (17 : ℝ) ≤ log t := by
        have hh : exp (17 : ℝ) ≤ t := interior_subset ht
        simpa only [log_exp] using log_le_log (exp_pos 17) hh
      apply div_nonpos_of_nonpos_of_nonneg
      · have hn : 33 - 2 * log t ≤ 0 := by linarith
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hn
      · exact pow_nonneg (by linarith) _
  have hb : f (exp 17) ≤ 100000000 := by
    have he1 : (1 : ℝ) < exp 17 := by linarith [add_one_le_exp (17 : ℝ)]
    have hf := F10_nonneg he1
    have hc : 0 ≤ 3 * (Nat.factorial 10 : ℝ) * exp 17 / log (exp 17) ^ 11 := by
      rw [log_exp]
      positivity
    have hl := li_exp17_upper hoffset hli2 hlog2
    dsimp [f]
    linarith
  have hh := hm (show exp (17 : ℝ) ∈ Set.Ici (exp 17) by simp) hx hx
  dsimp [f] at hb hh
  linarith

#print axioms actual_li_hasDerivAt
#print axioms F10_hasDerivAt
#print axioms actual_li_upper
end RamanujanPV.LiBarriers

namespace RamanujanPV.FiniteMiddle
open Real IEANTN
open RamanujanPV.Middle RamanujanPV.LiBarriers
set_option maxHeartbeats 4000000

noncomputable def S10 (L : ℝ) : ℝ := 1 + 1 / L ^ 1 + 2 / L ^ 2 + 6 / L ^ 3 + 24 / L ^ 4 + 120 / L ^ 5 + 720 / L ^ 6 + 5040 / L ^ 7 + 40320 / L ^ 8 + 362880 / L ^ 9
noncomputable def U10 (L : ℝ) : ℝ := S10 L + 10886400 / L ^ 10
noncomputable def T20 (L : ℝ) : ℝ := 1 + 2 / L ^ 1 + 5 / L ^ 2 + 16 / L ^ 3 + 65 / L ^ 4 + 326 / L ^ 5 + 1957 / L ^ 6 + 13700 / L ^ 7 + 109601 / L ^ 8 + 986410 / L ^ 9 + 6235301 / L ^ 10 + 28671512 / L ^ 11 + 104557345 / L ^ 12 + 321408686 / L ^ 13 + 867292805 / L ^ 14 + 2112105676 / L ^ 15 + 4734260417 / L ^ 16 + 9909524690 / L ^ 17 + 19582414021 / L ^ 18 + 36844580000 / L ^ 19 + 66449027201 / L ^ 20
noncomputable def positivePoly (L : ℝ) : ℝ := 1 + 14 / L ^ 1 + 145 / L ^ 2 + 1412 / L ^ 3 + 13985 / L ^ 4 + 145450 / L ^ 5 + 4548632 / L ^ 7 + 52993825 / L ^ 8 + 156419246 / L ^ 9 + 174192005 / L ^ 10
noncomputable def negativePoly (L : ℝ) : ℝ := 16533979 / L ^ 6 + 1429603124 / L ^ 11 + 16225688383 / L ^ 12 + 129088030510 / L ^ 13 + 989978776379 / L ^ 14 + 7864069084000 / L ^ 15 + 118447255932799 / L ^ 16
noncomputable def W (L : ℝ) : ℝ := L * exp (-L) * primeCounting (exp L)
noncomputable def normalizedGap (L : ℝ) : ℝ := L ^ 6 * exp (-2 * L) * RamanujanPV.gap (exp L)
noncomputable def totalError (b L : ℝ) : ℝ := piMajorant b L + 100000000 * L * exp (-L)

lemma scaled_F10 {L : ℝ} (hL : 0 < L) : L * exp (-L) * F10 (exp L) = S10 L := by
  norm_num [F10, S10, Finset.sum_range_succ, Nat.factorial, log_exp]
  rw [exp_neg]
  field_simp [hL.ne', (exp_pos L).ne']
  <;> ring

lemma W_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ W L := by
  unfold W
  exact mul_nonneg (mul_nonneg hL (exp_pos (-L)).le) (primeCounting_nonneg _)

/-- Convert the actual pi error and exact integral barriers to normalized
upper/lower pi information, retaining both signed sides for subsequent reuse. -/
theorem normalized_pi_bounds {b L : ℝ} (hL : 40 ≤ L)
    (herror : |piErrorLog L| ≤ piMajorant b L)
    (hoffset : LiOffsetIdentity) (hli2 : 0 ≤ IEANTN.li 2 ∧ IEANTN.li 2 ≤ 2)
    (hlog2 : (2 / 3 : ℝ) ≤ log 2) :
    S10 L - totalError b L ≤ W L ∧ W L ≤ U10 L + totalError b L := by
  have hL0 : 0 < L := by linarith
  have hx : (2 : ℝ) ≤ exp L := by linarith [add_one_le_exp L]
  have hscale : 0 ≤ L * exp (-L) := by positivity
  have hl := mul_le_mul_of_nonneg_left (actual_li_lower hx hoffset hli2.1 hlog2) hscale
  rw [mul_sub, scaled_F10 hL0] at hl
  have hu := mul_le_mul_of_nonneg_left
    (actual_li_upper (exp_le_exp.mpr (by linarith : (17 : ℝ) ≤ L)) hoffset hli2.2 hlog2) hscale
  have huId : L * exp (-L) *
      (F10 (exp L) + 3 * (Nat.factorial 10 : ℝ) * exp L / log (exp L) ^ 11 + 100000000) =
      U10 L + 100000000 * L * exp (-L) := by
    rw [mul_add, mul_add, scaled_F10 hL0]
    unfold U10
    rw [log_exp, exp_neg]
    norm_num
    field_simp [hL0.ne', (exp_pos L).ne']
    <;> ring
  rw [huId] at hu
  have hw : W L = piErrorLog L + L * exp (-L) * IEANTN.li (exp L) := by
    unfold W piErrorLog
    ring
  obtain ⟨heL, heU⟩ := abs_le.mp herror
  unfold totalError
  constructor <;> rw [hw] <;> nlinarith

/-- The shifted factorial series dominates its first21 positive binomial
coefficients. The exact remainder has a positive polynomial numerator. -/
theorem shifted_series_lower {L : ℝ} (hL : 1 < L) :
    T20 L ≤ L / (L - 1) * S10 (L - 1) := by
  have hL0 : 0 < L := by linarith
  have ht : 0 < L - 1 := by linarith
  have hid : L / (L - 1) * S10 (L - 1) - T20 L =
      (362880 + 7660800 * (L - 1) ^ 1 + 77056560 * (L - 1) ^ 2 + 491204160 * (L - 1) ^ 3 + 2226536040 * (L - 1) ^ 4 + 7632417264 * (L - 1) ^ 5 + 20542939710 * (L - 1) ^ 6 + 44490643808 * (L - 1) ^ 7 + 78819754063 * (L - 1) ^ 8 + 115493750422 * (L - 1) ^ 9) / (L ^ 20 * (L - 1) ^ 10) := by
    unfold S10 T20
    field_simp [hL0.ne', ht.ne']
    <;> ring
  have hn : 0 ≤ (362880 + 7660800 * (L - 1) ^ 1 + 77056560 * (L - 1) ^ 2 + 491204160 * (L - 1) ^ 3 + 2226536040 * (L - 1) ^ 4 + 7632417264 * (L - 1) ^ 5 + 20542939710 * (L - 1) ^ 6 + 44490643808 * (L - 1) ^ 7 + 78819754063 * (L - 1) ^ 8 + 115493750422 * (L - 1) ^ 9) := by positivity
  have hpos := div_nonneg hn (show 0 ≤ L ^ 20 * (L - 1) ^ 10 by positivity)
  rw [← hid] at hpos
  linarith

/-- This polynomial identity checks every retained numerical coefficient. -/
theorem model_polynomial_identity {L : ℝ} (hL : L ≠ 0) :
    L ^ 4 * (T20 L - U10 L ^ 2) = positivePoly L - negativePoly L := by
  unfold T20 U10 S10 positivePoly negativePoly
  field_simp [hL]
  <;> ring

theorem normalized_gap_identity {L : ℝ} (hL : 1 < L) :
    normalizedGap L = L ^ 4 * (L / (L - 1) * W (L - 1) - W L ^ 2) := by
  have hL0 : 0 < L := by linarith
  have ht : 0 < L - 1 := by linarith
  have he2 : exp (2 * L) = exp L ^ 2 := by
    rw [show 2 * L = L + L by ring, exp_add]
    ring
  have heminus : exp (-2 * L) = 1 / exp L ^ 2 := by
    rw [show -2 * L = -(2 * L) by ring, exp_neg, he2]
    simp only [one_div]
  unfold normalizedGap RamanujanPV.gap W
  rw [heminus]
  rw [log_exp, show exp L / exp 1 = exp (L - 1) by rw [exp_sub]]
  simp only [exp_neg, exp_sub, he2]
  field_simp [hL0.ne', ht.ne', (exp_pos L).ne', (exp_pos (1 : ℝ)).ne']
  <;> ring

/-- The recovered upper and lower pi information genuinely enters the actual
Ramanujan expression; a scalar certificate for a different function cannot pass. -/
theorem normalized_gap_lower {L up down : ℝ} (hL : 1 < L)
    (hu : W L ≤ U10 L + up) (hd : S10 (L - 1) - down ≤ W (L - 1)) :
    positivePoly L - negativePoly L -
      L ^ 4 * (L / (L - 1) * down + up * (2 * U10 L + up)) ≤ normalizedGap L := by
  have hL0 : 0 < L := by linarith
  have ht : 0 < L - 1 := by linarith
  have hs := shifted_series_lower hL
  have hd' := mul_le_mul_of_nonneg_left hd (div_pos hL0 ht).le
  have hdown : T20 L - L / (L - 1) * down ≤ L / (L - 1) * W (L - 1) := by
    nlinarith
  have hup : W L ^ 2 ≤ (U10 L + up) ^ 2 := pow_le_pow_left₀ (W_nonneg hL0.le) hu 2
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub hdown hup) (pow_nonneg hL0.le 4)
  rw [← normalized_gap_identity hL] at hh
  have hid : L ^ 4 * (T20 L - L / (L - 1) * down - (U10 L + up) ^ 2) =
      positivePoly L - negativePoly L -
        L ^ 4 * (L / (L - 1) * down + up * (2 * U10 L + up)) := by
    rw [← model_polynomial_identity hL0.ne']
    ring
  rw [hid] at hh
  exact hh

#print axioms normalized_pi_bounds
#print axioms shifted_series_lower
#print axioms model_polynomial_identity
#print axioms normalized_gap_lower
end RamanujanPV.FiniteMiddle

namespace RamanujanPV.FiniteMiddle
open Real IEANTN
open RamanujanPV.Middle
set_option maxHeartbeats 4000000

lemma piMajorant_simplified (b L : ℝ) :
    piMajorant b L = b * (1 + L / 1600) + 116 * (1 + L / 800) * exp (-L / 2) +
      L / 40 * exp (40 - L) * ((5 / 1000000000 : ℝ) + b + 116 * exp (-20)) := by
  have he : exp (-L) * exp L = 1 := by rw [← exp_add]; simp
  have hh : exp (-L) * exp (L / 2) = exp (-L / 2) := by
    rw [← exp_add]
    congr 1
    ring
  unfold piMajorant
  calc
    _ = b + 116 * exp (-L / 2) +
      L / 40 * exp (40 - L) * ((5 / 1000000000 : ℝ) + b + 116 * exp (-20)) +
      b * L / 1600 * (exp (-L) * exp L) +
      116 * L / 800 * (exp (-L) * exp (L / 2)) := by ring
    _ = _ := by rw [he, hh]; ring

noncomputable def rho : ℝ := 500 / 1359
noncomputable def b0 : ℝ := 131 / 125000000000000
noncomputable def expHalfBound (a : ℕ) : ℝ :=
  if a % 2 = 0 then rho ^ (a / 2) else (2 / 3 : ℝ) * rho ^ (a / 2)

lemma exp_neg_nat_upper (n : ℕ) : exp (-(n : ℝ)) ≤ rho ^ n := by
  have he : (1359 / 500 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have hp : (1359 / 500 : ℝ) ^ n ≤ exp (n : ℝ) := by
    rw [← exp_one_pow n]
    exact pow_le_pow_left₀ (by norm_num) he n
  rw [exp_neg, ← one_div]
  calc
    1 / exp (n : ℝ) ≤ 1 / (1359 / 500 : ℝ) ^ n :=
      one_div_le_one_div_of_le (by positivity) hp
    _ = rho ^ n := by unfold rho; rw [← one_div_pow]; norm_num

lemma exp_neg_half_upper : exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
  rw [exp_neg, ← one_div]
  have he : (3 / 2 : ℝ) ≤ exp (1 / 2 : ℝ) := by linarith [add_one_le_exp (1 / 2 : ℝ)]
  exact (one_div_le_one_div_of_le (by norm_num) he).trans (by norm_num)

lemma exp_neg_half_nat_upper (n : ℕ) : exp (-(n : ℝ) / 2) ≤ expHalfBound n := by
  unfold expHalfBound
  by_cases hm : n % 2 = 0
  · rw [if_pos hm]
    have hn : n = 2 * (n / 2) := by omega
    have hnr : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hn
    rw [show -(n : ℝ) / 2 = -((n / 2 : ℕ) : ℝ) by linarith]
    exact exp_neg_nat_upper _
  · rw [if_neg hm]
    have hn : n = 2 * (n / 2) + 1 := by omega
    have hnr : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hn
    rw [show -(n : ℝ) / 2 = -((n / 2 : ℕ) : ℝ) + -(1 / 2 : ℝ) by linarith, exp_add]
    have h := mul_le_mul (exp_neg_nat_upper (n / 2)) exp_neg_half_upper
      (exp_pos (-(1 / 2 : ℝ))).le (by unfold rho; positivity)
    simpa only [mul_comm] using h

noncomputable def cellError (a b : ℕ) : ℝ :=
  b0 * (1 + (b : ℝ) / 1600) + 116 * (1 + (b : ℝ) / 800) * expHalfBound a +
    (b : ℝ) / 40 * rho ^ (a - 40) * ((5 / 1000000000 : ℝ) + b0 + 116 * rho ^ 20) +
    100000000 * b * rho ^ a

lemma expHalfBound_nonneg (a : ℕ) : 0 ≤ expHalfBound a := by
  unfold expHalfBound
  split_ifs <;> unfold rho <;> positivity

lemma cellError_nonneg (a b : ℕ) : 0 ≤ cellError a b := by
  unfold cellError b0
  have hh := expHalfBound_nonneg a
  unfold rho
  positivity

/-- A whole-cell enclosure. Exponential bounds are monotonic inequalities,
never sampled evaluations. All arithmetic endpoint bounds are kernel rational proofs. -/
theorem totalError_le_cellError {a b : ℕ} (ha : 40 ≤ a) {L : ℝ}
    (hLa : (a : ℝ) ≤ L) (hLb : L ≤ (b : ℝ)) : totalError b0 L ≤ cellError a b := by
  have haR : (40 : ℝ) ≤ a := by exact_mod_cast ha
  have hL0 : 0 ≤ L := by linarith
  have heh : exp (-L / 2) ≤ expHalfBound a :=
    (exp_le_exp.mpr (by linarith)).trans (exp_neg_half_nat_upper a)
  have hes : exp (40 - L) ≤ rho ^ (a - 40) := by
    have har : ((a - 40 : ℕ) : ℝ) = (a : ℝ) - 40 := by rw [Nat.cast_sub ha]; norm_num
    have h := exp_neg_nat_upper (a - 40)
    rw [har] at h
    exact (exp_le_exp.mpr (by linarith)).trans h
  have hef : exp (-L) ≤ rho ^ a :=
    (exp_le_exp.mpr (by linarith)).trans (exp_neg_nat_upper a)
  have he20 : exp (-20 : ℝ) ≤ rho ^ 20 := by simpa using exp_neg_nat_upper 20
  rw [totalError, piMajorant_simplified]
  unfold cellError
  have hb0 : 0 ≤ b0 := by unfold b0; norm_num
  have hr : 0 ≤ rho := by unfold rho; norm_num
  gcongr

lemma positivePoly_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    positivePoly b ≤ positivePoly a := by unfold positivePoly; gcongr
lemma negativePoly_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    negativePoly b ≤ negativePoly a := by unfold negativePoly; gcongr
lemma U10_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : U10 b ≤ U10 a := by
  unfold U10 S10
  gcongr
lemma U10_nonneg {L : ℝ} (hL : 0 < L) : 0 ≤ U10 L := by unfold U10 S10; positivity

noncomputable def cellMargin (a b : ℕ) : ℝ := positivePoly b - negativePoly a -
  (b : ℝ) ^ 4 * ((b : ℝ) / ((a : ℝ) - 1) * cellError (a - 1) (b - 1) +
    cellError a b * (2 * U10 a + cellError a b))

/-- Five complete exact-arithmetic checks, preserving the whole intervals.
These kernel rational certificates are analytic arithmetic, not labelled source-first PV. -/
theorem five_numeric_margins :
    (37 / 200 : ℝ) < cellMargin 43 44 ∧
    (37 / 200 : ℝ) < cellMargin 44 45 ∧
    (37 / 200 : ℝ) < cellMargin 45 50 ∧
    (37 / 200 : ℝ) < cellMargin 50 70 ∧
    (37 / 200 : ℝ) < cellMargin 70 169 := by
  norm_num [cellMargin, positivePoly, negativePoly, U10, S10, cellError, b0, rho, expHalfBound]

#print axioms totalError_le_cellError
#print axioms five_numeric_margins
end RamanujanPV.FiniteMiddle

namespace RamanujanPV.FiniteMiddle
open Real IEANTN
open RamanujanPV.Middle
set_option maxHeartbeats 4000000

/-- Reusable whole-cell analytic transport from the recovered signed pi data.
Its hypotheses are actual pi-error bounds and prime-free integral normalization,
not a positivity oracle for the target function. -/
theorem normalized_gap_on_cell {a b : ℕ} (ha : 41 ≤ a) {L : ℝ}
    (hLa : (a : ℝ) ≤ L) (hLb : L ≤ (b : ℝ))
    (herror : ∀ t : ℝ, 40 ≤ t → |piErrorLog t| ≤ piMajorant b0 t)
    (hoffset : LiOffsetIdentity) (hli2 : 0 ≤ IEANTN.li 2 ∧ IEANTN.li 2 ≤ 2)
    (hlog2 : (2 / 3 : ℝ) ≤ log 2) : cellMargin a b ≤ normalizedGap L := by
  have haR : (41 : ℝ) ≤ a := by exact_mod_cast ha
  have hL40 : (40 : ℝ) ≤ L := by linarith
  have hL1 : 1 < L := by linarith
  have ha0 : (0 : ℝ) < a := by linarith
  have hL0 : 0 < L := by linarith
  have hbN : 41 ≤ b := by exact_mod_cast (haR.trans (hLa.trans hLb))
  have haSub : (((a - 1 : ℕ) : ℝ)) = (a : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ a)]; norm_num
  have hbSub : (((b - 1 : ℕ) : ℝ)) = (b : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ b)]; norm_num
  have hA := normalized_pi_bounds hL40 (herror L hL40) hoffset hli2 hlog2
  have hD := normalized_pi_bounds (by linarith : 40 ≤ L - 1)
    (herror (L - 1) (by linarith)) hoffset hli2 hlog2
  have huErr := totalError_le_cellError (a:=a) (b:=b) (by omega) hLa hLb
  have hdErr := totalError_le_cellError (a:=a-1) (b:=b-1) (L:=L-1) (by omega)
    (by rw [haSub]; linarith) (by rw [hbSub]; linarith)
  have hu : W L ≤ U10 L + cellError a b := hA.2.trans (by linarith)
  have hd : S10 (L - 1) - cellError (a - 1) (b - 1) ≤ W (L - 1) := by
    linarith [hD.1]
  have hg := normalized_gap_lower hL1 hu hd
  have hp := positivePoly_antitone hL0 hLb
  have hn := negativePoly_antitone ha0 hLa
  have hU := U10_antitone ha0 hLa
  have hfac : L / (L - 1) ≤ (b : ℝ) / ((a : ℝ) - 1) := by
    apply div_le_div₀ (by linarith : 0 ≤ (b : ℝ)) hLb (by linarith : 0 < (a : ℝ) - 1)
    linarith
  have hpow : L ^ 4 ≤ (b : ℝ) ^ 4 := pow_le_pow_left₀ hL0.le hLb 4
  have hUp0 := cellError_nonneg a b
  have hDown0 := cellError_nonneg (a - 1) (b - 1)
  have hU0 := U10_nonneg hL0
  have hLoss : L ^ 4 * (L / (L - 1) * cellError (a - 1) (b - 1) +
      cellError a b * (2 * U10 L + cellError a b)) ≤
      (b : ℝ) ^ 4 * ((b : ℝ) / ((a : ℝ) - 1) * cellError (a - 1) (b - 1) +
      cellError a b * (2 * U10 a + cellError a b)) := by
    gcongr
  unfold cellMargin
  linarith

/-- The five checked cells cover the complete closed intermediate interval. -/
theorem normalized_gap_gt_37_200 {L : ℝ} (hL : 43 ≤ L) (hL169 : L ≤ 169)
    (herror : ∀ t : ℝ, 40 ≤ t → |piErrorLog t| ≤ piMajorant b0 t)
    (hoffset : LiOffsetIdentity) (hli2 : 0 ≤ IEANTN.li 2 ∧ IEANTN.li 2 ≤ 2)
    (hlog2 : (2 / 3 : ℝ) ≤ log 2) : (37 / 200 : ℝ) < normalizedGap L := by
  obtain ⟨h43,h44,h45,h50,h70⟩ := five_numeric_margins
  by_cases hc44 : L ≤ 44
  · exact h43.trans_le (normalized_gap_on_cell (a:=43) (b:=44) (by norm_num)
      (by norm_num; exact hL) (by norm_num; exact hc44) herror hoffset hli2 hlog2)
  by_cases hc45 : L ≤ 45
  · exact h44.trans_le (normalized_gap_on_cell (a:=44) (b:=45) (by norm_num)
      (by norm_num; linarith) (by norm_num; exact hc45) herror hoffset hli2 hlog2)
  by_cases hc50 : L ≤ 50
  · exact h45.trans_le (normalized_gap_on_cell (a:=45) (b:=50) (by norm_num)
      (by norm_num; linarith) (by norm_num; exact hc50) herror hoffset hli2 hlog2)
  by_cases hc70 : L ≤ 70
  · exact h50.trans_le (normalized_gap_on_cell (a:=50) (b:=70) (by norm_num)
      (by norm_num; linarith) (by norm_num; exact hc70) herror hoffset hli2 hlog2)
  exact h70.trans_le (normalized_gap_on_cell (a:=70) (b:=169) (by norm_num)
    (by norm_num; linarith) (by norm_num; exact hL169) herror hoffset hli2 hlog2)

theorem gap_of_normalized_gap {L : ℝ} (hL : 0 < L)
    (hg : (37 / 200 : ℝ) < normalizedGap L) :
    (37 / 200 : ℝ) * exp L ^ 2 / L ^ 6 < RamanujanPV.gap (exp L) := by
  have hs : 0 < L ^ 6 * exp (-2 * L) := by positivity
  apply (mul_lt_mul_iff_right₀ hs).mp
  have hId : (L ^ 6 * exp (-2 * L)) * ((37 / 200 : ℝ) * exp L ^ 2 / L ^ 6) = 37 / 200 := by
    have he2 : exp (2 * L) = exp L ^ 2 := by rw [show 2 * L = L + L by ring, exp_add]; ring
    rw [show -2 * L = -(2 * L) by ring, exp_neg, he2]
    field_simp [hL.ne', (exp_pos L).ne']
  rw [hId]
  exact hg

/-- An actual whole-real-interval quantitative middle theorem. The only source
inputs are CH2, Dusart, a Büthe anchor, and the prime-free li normalization/bounds. -/
theorem actual_middle_gap {x : ℝ} (hx43 : exp 43 ≤ x) (hx169 : x ≤ exp 169)
    (hpsi : CH2PsiInput b0) (hpower : DusartPowerInput)
    (hanchor : |piErrorLog 40| ≤ (5 / 1000000000 : ℝ))
    (hoffset : LiOffsetIdentity) (hli2 : 0 ≤ IEANTN.li 2 ∧ IEANTN.li 2 ≤ 2)
    (hlog2 : (2 / 3 : ℝ) ≤ log 2) :
    (37 / 200 : ℝ) * x ^ 2 / log x ^ 6 < RamanujanPV.gap x := by
  have hx0 : 0 < x := (exp_pos 43).trans_le hx43
  have hL : (43 : ℝ) ≤ log x := by simpa using log_le_log (exp_pos 43) hx43
  have hLU : log x ≤ (169 : ℝ) := by simpa using log_le_log hx0 hx169
  have herr : ∀ t : ℝ, 40 ≤ t → |piErrorLog t| ≤ piMajorant b0 t := by
    intro t ht
    exact pi_error_from_CH2_Dusart_Buthe (by unfold b0; norm_num) ht hpsi hpower hanchor hoffset
  have hg := gap_of_normalized_gap (by linarith : 0 < log x)
    (normalized_gap_gt_37_200 hL hLU herr hoffset hli2 hlog2)
  simpa only [exp_log hx0] using hg

#print axioms normalized_gap_on_cell
#print axioms normalized_gap_gt_37_200
#print axioms actual_middle_gap
end RamanujanPV.FiniteMiddle

namespace RamanujanPV.FiniteMiddle
open Real IEANTN
open RamanujanPV.Middle

/-- Büthe Theorem2(1.9), with the source's polynomial coefficient and finite
range retained exactly, instead of assuming an endpoint prime count. -/
def ButheDeficit19 : Prop := ∀ t : ℝ, 2 ≤ t → t ≤ 10000000000000000000 →
  IEANTN.li t - sqrt t / log t * ((39 / 20 : ℝ) + (39 / 10 : ℝ) / log t +
    (39 / 2 : ℝ) / log t ^ 2) ≤ primeCounting t

def ButheBelow19 : Prop := ∀ t : ℝ, 2 ≤ t → t ≤ 10000000000000000000 →
  primeCounting t ≤ IEANTN.li t

/-- The concrete a=40 pi-error anchor is derived from the exact published Büthe
inequalities and kernel rational bounds for exp. It is not a new numerical premise. -/
theorem anchor40_of_Buthe (hbuthe : ButheDeficit19) (hbelow : ButheBelow19) :
    |piErrorLog 40| ≤ (5 / 1000000000 : ℝ) := by
  have he2 : (2 : ℝ) ≤ exp 40 := by linarith [add_one_le_exp (40 : ℝ)]
  have he1 : exp 1 ≤ (68 / 25 : ℝ) := by linarith [exp_one_lt_d9]
  have he40 : exp (40 : ℝ) ≤ (68 / 25 : ℝ)^40 := by
    have h := pow_le_pow_left₀ (exp_pos 1).le he1 40
    convert! h using 1 <;> norm_num [← exp_nat_mul]
  have hetop : exp (40 : ℝ) ≤ 10000000000000000000 := he40.trans (by norm_num)
  have hP := hbelow (exp 40) he2 hetop
  have hD := hbuthe (exp 40) he2 hetop
  have habs : |primeCounting (exp 40) - IEANTN.li (exp 40)| =
      IEANTN.li (exp 40) - primeCounting (exp 40) := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hP)]
  have hscaled := mul_le_mul_of_nonneg_left
    (show IEANTN.li (exp 40) - primeCounting (exp 40) ≤
      sqrt (exp 40) / log (exp 40) * ((39 / 20 : ℝ) + (39 / 10 : ℝ) / log (exp 40) +
        (39 / 2 : ℝ) / log (exp 40) ^ 2) by linarith)
    (show 0 ≤ (40 : ℝ) * exp (-40) by positivity)
  rw [log_exp, ← exp_half] at hscaled
  norm_num only [show (40 : ℝ) / 2 = 20 by norm_num] at hscaled
  have heprod : exp (-40 : ℝ) * exp 20 = exp (-20) := by rw [← exp_add]; norm_num
  have hid : (40 : ℝ) * exp (-40) * (exp 20 / 40 *
      (6591 / 3200 : ℝ)) =
      (6591 / 3200 : ℝ) * exp (-20) := by
    calc
      _ = (6591 / 3200 : ℝ) *
          (exp (-40) * exp 20) := by ring
      _ = _ := by rw [heprod]
  rw [hid] at hscaled
  have he20 : exp (-20 : ℝ) ≤ rho ^ 20 := by simpa using exp_neg_nat_upper 20
  have hn : (6591 / 3200 : ℝ) *
      exp (-20) ≤ (5 / 1000000000 : ℝ) := by
    calc
      _ ≤ (6591 / 3200 : ℝ) * rho ^ 20 := by gcongr
      _ ≤ _ := by unfold rho; norm_num
  unfold piErrorLog
  rw [abs_mul, abs_of_pos (show 0 < (40 : ℝ) * exp (-40) by positivity), habs]
  exact hscaled.trans hn

/-- Safe rational rounding of the original CH2 Corollary1.3 coefficient.
The exact original statement is the hypothesis, not its desired downstream effect. -/
theorem CH2PsiInput_of_original
    (hsource : ∀ x : ℝ, 1 ≤ x → |Chebyshev.psi x - x| ≤
      Real.pi / (3 * (10 : ℝ)^12) * x + (113.67 : ℝ) * sqrt x) : CH2PsiInput b0 := by
  intro x hx
  have hc : Real.pi / (3 * (10 : ℝ)^12) ≤ b0 := by
    unfold b0
    have hp : Real.pi < 3.144 := lt_trans Real.pi_lt_d4 (by norm_num)
    norm_num
    linarith
  exact (hsource x hx).trans (by gcongr)

/-- The completed bounded middle theorem, exposing only the named exact source
inputs. The Büthe anchor and every five-cell arithmetic obligation are supplied. -/
theorem actual_middle_gap_from_sources {x : ℝ} (hx43 : exp 43 ≤ x) (hx169 : x ≤ exp 169)
    (hpsi : ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤
      Real.pi / (3 * (10 : ℝ)^12) * t + (113.67 : ℝ) * sqrt t)
    (hpower : DusartPowerInput) (hbuthe : ButheDeficit19) (hbelow : ButheBelow19)
    (hoffset : LiOffsetIdentity) (hli2 : 0 ≤ IEANTN.li 2 ∧ IEANTN.li 2 ≤ 2)
    (hlog2 : (2 / 3 : ℝ) ≤ log 2) :
    (37 / 200 : ℝ) * x ^ 2 / log x ^ 6 < RamanujanPV.gap x :=
  actual_middle_gap hx43 hx169 (CH2PsiInput_of_original hpsi) hpower
    (anchor40_of_Buthe hbuthe hbelow) hoffset hli2 hlog2

#print axioms anchor40_of_Buthe
#print axioms CH2PsiInput_of_original
#print axioms actual_middle_gap_from_sources
end RamanujanPV.FiniteMiddle
