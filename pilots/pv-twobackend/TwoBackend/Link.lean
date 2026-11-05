/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import IEANTN.Vocabulary.PowerError
import IntegralBounds
import Numerics
import ForwardRamanujan.Math
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The data link: a `Li`-form bound for `π` in the five-term shape

Agent A's provider bounds `π` against the offset logarithmic integral:
`IEANTN.HasPowerLogBound IEANTN.Eπ A 0 (7/8) (exp 300)`, that is
`|π(x) − Li(x)| ≤ A · x^(7/8) / log x` for `x ≥ e^300`. The Ramanujan budget program takes `π` in
the five-term shape `π(x) ∈ mainTerm(x) + [m, M] · x / log⁶ x` (`ForwardRamanujan.PiInput`).

This file converts the first into the second, with `(m, M) = (119.99, 122.5)` on `x > e^300`:

* `Li = mainTerm − K₅ + 120·I₆` by five integrations by parts (`logIntegral_recurrence`);
* `I₆ ≥ x/log⁶x − 2/log⁶2`, and `I₆ ≤ x/log⁶x (1 + 6/L + … ) + …` by five more and a split at `√x`;
* at `log x ≥ 300` every lower-order term, and Agent A's error itself, is at most `10⁻³ · x/log⁶x`.

Nothing here is numerical evaluation of a program: it is analysis with explicit constants, checked by
the kernel. The two executed programs of the chain are Agent A's dyadic evaluator (before this
file) and the selected C budget program (after it).
-/

namespace PVTwoBackend

open Real IEANTN DudekPlattNumerics.Calculus

/-- The constant left at the lower endpoint `2` by five integrations by parts. -/
noncomputable def K5 : ℝ :=
  2 * (1 / log 2 + 1 / log 2 ^ 2 + 2 / log 2 ^ 3 + 6 / log 2 ^ 4 + 24 / log 2 ^ 5)

theorem Li_eq_logIntegral (x : ℝ) : Li x = logIntegral 1 x := by
  simp [Li, logIntegral]

/-- Five integrations by parts from the lower endpoint 2. -/
theorem Li_expansion {x : ℝ} (hx : 2 ≤ x) :
    Li x = DudekPlatt.v3.mainTerm x - K5 + 120 * logIntegral 6 x := by
  have r0 := logIntegral_recurrence 0 hx
  have r1 := logIntegral_recurrence 1 hx
  have r2 := logIntegral_recurrence 2 hx
  have r3 := logIntegral_recurrence 3 hx
  have r4 := logIntegral_recurrence 4 hx
  rw [Li_eq_logIntegral]
  simp only [DudekPlatt.v3.mainTerm, K5, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.factorial] at r0 r1 r2 r3 r4 ⊢
  norm_num at r0 r1 r2 r3 r4 ⊢
  linear_combination r0 + r1 + 2 * r2 + 6 * r3 + 24 * r4

theorem I6_ge {x : ℝ} (hx : 2 ≤ x) : x / log x ^ 6 - 2 / log 2 ^ 6 ≤ logIntegral 6 x := by
  have r5 := logIntegral_recurrence 5 hx
  have h7 := logIntegral_nonneg 7 hx
  norm_num at r5
  linarith

theorem I6_le {x : ℝ} (hx : 4 ≤ x) :
    logIntegral 6 x ≤ x / log x ^ 6 + 6 * (x / log x ^ 7) + 42 * (x / log x ^ 8) +
      336 * (x / log x ^ 9) + 3024 * (x / log x ^ 10) +
      30240 * (sqrt x / log 2 ^ 11 + 2048 * (x / log x ^ 11)) := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have r5 := logIntegral_recurrence 5 hx2
  have r6 := logIntegral_recurrence 6 hx2
  have r7 := logIntegral_recurrence 7 hx2
  have r8 := logIntegral_recurrence 8 hx2
  have r9 := logIntegral_recurrence 9 hx2
  have hs := logIntegral_sqrt_bound 11 hx
  have hl : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have c6 : 0 ≤ 2 / log (2 : ℝ) ^ 6 := by positivity
  have c7 : 0 ≤ 2 / log (2 : ℝ) ^ 7 := by positivity
  have c8 : 0 ≤ 2 / log (2 : ℝ) ^ 8 := by positivity
  have c9 : 0 ≤ 2 / log (2 : ℝ) ^ 9 := by positivity
  have c10 : 0 ≤ 2 / log (2 : ℝ) ^ 10 := by positivity
  norm_num at r5 r6 r7 r8 r9 hs
  have e11 : 2048 * x / log x ^ 11 = 2048 * (x / log x ^ 11) := by ring
  rw [e11] at hs
  linarith

/-! ### Scalar facts at `log x ≥ 300` -/

theorem log_two_inv_lt : 1 / log (2 : ℝ) < 3 / 2 := by
  have h := DudekPlattNumerics.v4.Numerics.hlog2_proof
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- `K₅` and the next endpoint constant, together, are below 3200. -/
theorem endpoint_le : K5 + 240 / log (2 : ℝ) ^ 6 ≤ 3200 := by
  have h := log_two_inv_lt
  have hp : 0 < 1 / log (2 : ℝ) := by
    have := DudekPlattNumerics.v4.Numerics.hlog2_proof
    positivity
  set t := 1 / log (2 : ℝ) with ht
  have e : K5 + 240 / log (2 : ℝ) ^ 6 =
      2 * (t + t ^ 2 + 2 * t ^ 3 + 6 * t ^ 4 + 24 * t ^ 5) + 240 * t ^ 6 := by
    simp only [K5, ht]
    field_simp
  rw [e]
  have h2 : t ^ 2 ≤ (3 / 2) ^ 2 := by gcongr
  have h3 : t ^ 3 ≤ (3 / 2) ^ 3 := by gcongr
  have h4 : t ^ 4 ≤ (3 / 2) ^ 4 := by gcongr
  have h5 : t ^ 5 ≤ (3 / 2) ^ 5 := by gcongr
  have h6 : t ^ 6 ≤ (3 / 2) ^ 6 := by gcongr
  norm_num at h2 h3 h4 h5 h6
  nlinarith

/-- `L⁶ e^{−L} ≤ 300⁶ / 2¹⁰⁰` for `L ≥ 300` (weak, but `norm_num` evaluates `2¹⁰⁰`). -/
theorem poly6_exp_le {L : ℝ} (hL : 300 ≤ L) : L ^ 6 * exp (-L) ≤ 300 ^ 6 / 2 ^ 100 := by
  have hd := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 6 (c := 1) (L0 := 300)
    (by norm_num) (by norm_num) hL
  have he := DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 100
  have hm : exp (-300 : ℝ) ≤ exp (-((100 : ℕ) : ℝ)) := exp_le_exp.mpr (by norm_num)
  simp only [neg_mul, one_mul] at hd
  calc L ^ 6 * exp (-L) ≤ 300 ^ 6 * exp (-300) := hd
    _ ≤ 300 ^ 6 * (1 / 2 ^ 100) := by gcongr; exact hm.trans he
    _ = 300 ^ 6 / 2 ^ 100 := by ring

/-- `L⁶ e^{−L/2} ≤ 300⁶ / 2¹⁵⁰` for `L ≥ 300`. -/
theorem poly6_exp_half_le {L : ℝ} (hL : 300 ≤ L) :
    L ^ 6 * exp (-(1 / 2) * L) ≤ 300 ^ 6 / 2 ^ 150 := by
  have hd := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 6 (c := 1 / 2) (L0 := 300)
    (by norm_num) (by norm_num) hL
  have he := DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 150
  calc L ^ 6 * exp (-(1 / 2) * L) ≤ 300 ^ 6 * exp (-(1 / 2) * 300) := hd
    _ = 300 ^ 6 * exp (-((150 : ℕ) : ℝ)) := by norm_num
    _ ≤ 300 ^ 6 * (1 / 2 ^ 150) := by gcongr
    _ = 300 ^ 6 / 2 ^ 150 := by ring

/-- `L⁵ e^{−L/8} ≤ 296⁵ · 0.3678794412³⁷` for `L ≥ 296`. -/
theorem poly5_exp_eighth_le {L : ℝ} (hL : 296 ≤ L) :
    L ^ 5 * exp (-(1 / 8) * L) ≤ 296 ^ 5 * 0.3678794412 ^ 37 := by
  have hd := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 5 (c := 1 / 8) (L0 := 296)
    (by norm_num) (by norm_num) hL
  have he : exp (-(1 / 8) * 296 : ℝ) = exp (-1) ^ 37 := by
    rw [← exp_nat_mul]
    norm_num
  have h1 := Real.exp_neg_one_lt_d9
  have h0 : 0 ≤ exp (-1 : ℝ) := (exp_pos _).le
  calc L ^ 5 * exp (-(1 / 8) * L) ≤ 296 ^ 5 * exp (-(1 / 8) * 296) := hd
    _ = 296 ^ 5 * exp (-1) ^ 37 := by rw [he]
    _ ≤ 296 ^ 5 * 0.3678794412 ^ 37 := by gcongr

/-- The lower-order terms of `I₆`, relative to `x / log⁶ x`, at `log x ≥ 300`. -/
theorem tail_coeff_le {L : ℝ} (hL : 300 ≤ L) :
    6 / L + 42 / L ^ 2 + 336 / L ^ 3 + 3024 / L ^ 4 + 30240 * 2048 / L ^ 5 ≤ 206 / 10000 := by
  have hL0 : 0 < L := by linarith
  have h1 : 6 / L ≤ 6 / 300 := by gcongr
  have h2 : 42 / L ^ 2 ≤ 42 / 300 ^ 2 := by gcongr
  have h3 : 336 / L ^ 3 ≤ 336 / 300 ^ 3 := by gcongr
  have h4 : 3024 / L ^ 4 ≤ 3024 / 300 ^ 4 := by gcongr
  have h5 : 30240 * 2048 / L ^ 5 ≤ 30240 * 2048 / 300 ^ 5 := by gcongr
  have : 6 / (300 : ℝ) + 42 / 300 ^ 2 + 336 / 300 ^ 3 + 3024 / 300 ^ 4 + 30240 * 2048 / 300 ^ 5
      ≤ 206 / 10000 := by norm_num
  linarith

/-! ### `Li` against the five-term main term -/

theorem Li_sub_mainTerm_le {x : ℝ} (hx : exp 300 ≤ x) :
    Li x - DudekPlatt.v3.mainTerm x ≤ 12249 / 100 * (x / log x ^ 6) := by
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hL : 300 ≤ log x := by
    have := log_le_log (exp_pos _) hx
    rwa [log_exp] at this
  have hL0 : 0 < log x := by linarith
  have hx4 : (4 : ℝ) ≤ x := by
    have : (4 : ℝ) ≤ exp 300 := by
      have := add_one_le_exp (300 : ℝ)
      linarith
    linarith
  have hexp := Li_expansion (show (2 : ℝ) ≤ x by linarith)
  have hI := I6_le hx4
  have hK : 0 ≤ K5 := by
    have hl : 0 < log (2 : ℝ) := log_pos (by norm_num)
    unfold K5
    positivity
  set u := x / log x ^ 6 with hu
  have hu0 : 0 < u := by positivity
  -- each lower-order term as a multiple of u
  have e7 : x / log x ^ 7 = u / log x := by rw [hu]; field_simp
  have e8 : x / log x ^ 8 = u / log x ^ 2 := by rw [hu]; field_simp
  have e9 : x / log x ^ 9 = u / log x ^ 3 := by rw [hu]; field_simp
  have e10 : x / log x ^ 10 = u / log x ^ 4 := by rw [hu]; field_simp
  have e11 : x / log x ^ 11 = u / log x ^ 5 := by rw [hu]; field_simp
  rw [e7, e8, e9, e10, e11] at hI
  -- the √x term is negligible: √x / log 2¹¹ ≤ 10⁻¹² u
  have hsq : sqrt x / log 2 ^ 11 ≤ 1 / 10 ^ 12 * u := by
    have hsx : sqrt x = exp (log x / 2) := by
      rw [sqrt_eq_rpow, rpow_def_of_pos hx0]
      ring_nf
    have hxL : x = exp (log x) := (exp_log hx0).symm
    have hp := poly6_exp_half_le hL
    have hl := log_two_inv_lt
    have hlp : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have hinv : 1 / log (2 : ℝ) ^ 11 ≤ (3 / 2) ^ 11 := by
      rw [one_div, ← inv_pow]
      have : (log (2 : ℝ))⁻¹ ≤ 3 / 2 := by rw [← one_div]; exact hl.le
      gcongr
    -- √x / u = L⁶ e^{-L/2}
    have key : sqrt x = (log x ^ 6 * exp (-(1 / 2) * log x)) * u := by
      have hL6 : log x ^ 6 ≠ 0 := by positivity
      rw [hu, hsx]
      calc exp (log x / 2) = exp (-(1 / 2) * log x) * exp (log x) := by
            rw [← exp_add]; ring_nf
        _ = exp (-(1 / 2) * log x) * x := by rw [← hxL]
        _ = log x ^ 6 * exp (-(1 / 2) * log x) * (x / log x ^ 6) := by field_simp
    rw [key]
    have hpos : 0 ≤ log x ^ 6 * exp (-(1 / 2) * log x) := by positivity
    calc log x ^ 6 * exp (-(1 / 2) * log x) * u / log 2 ^ 11
        = (log x ^ 6 * exp (-(1 / 2) * log x)) * (1 / log 2 ^ 11) * u := by ring
      _ ≤ (300 ^ 6 / 2 ^ 150) * (3 / 2) ^ 11 * u := by gcongr
      _ ≤ 1 / 10 ^ 12 * u := by
        apply mul_le_mul_of_nonneg_right _ hu0.le
        norm_num
  have ht := tail_coeff_le hL
  have ht' : 6 * (u / log x) + 42 * (u / log x ^ 2) + 336 * (u / log x ^ 3) +
      3024 * (u / log x ^ 4) + 30240 * (2048 * (u / log x ^ 5)) ≤ 206 / 10000 * u := by
    have : 6 * (u / log x) + 42 * (u / log x ^ 2) + 336 * (u / log x ^ 3) +
        3024 * (u / log x ^ 4) + 30240 * (2048 * (u / log x ^ 5)) =
        (6 / log x + 42 / log x ^ 2 + 336 / log x ^ 3 + 3024 / log x ^ 4 +
          30240 * 2048 / log x ^ 5) * u := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right ht hu0.le
  linarith

theorem mainTerm_add_le_Li {x : ℝ} (hx : exp 300 ≤ x) :
    DudekPlatt.v3.mainTerm x + 120 * (x / log x ^ 6) - 1 / 1000 * (x / log x ^ 6) ≤ Li x := by
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hL : 300 ≤ log x := by
    have := log_le_log (exp_pos _) hx
    rwa [log_exp] at this
  have hexp := Li_expansion (show (2 : ℝ) ≤ x by
    have : (2 : ℝ) ≤ exp 300 := by
      have := add_one_le_exp (300 : ℝ)
      linarith
    linarith)
  have hI := I6_ge (show (2 : ℝ) ≤ x by
    have : (2 : ℝ) ≤ exp 300 := by
      have := add_one_le_exp (300 : ℝ)
      linarith
    linarith)
  have hE := endpoint_le
  -- 3200 ≤ (1/1000) · x / log⁶ x, from L⁶ e^{−L} ≤ 300⁶/2¹⁰⁰
  have hp := poly6_exp_le hL
  have hxL : x = exp (log x) := (exp_log hx0).symm
  have hL0 : 0 < log x := by linarith
  have hsmall : 3200 ≤ 1 / 1000 * (x / log x ^ 6) := by
    have hq : log x ^ 6 / x ≤ 300 ^ 6 / 2 ^ 100 := by
      have : log x ^ 6 / x = log x ^ 6 * exp (-log x) := by
        conv_lhs => rw [hxL]
        rw [exp_neg, div_eq_mul_inv, exp_log hx0]
      rw [this]
      exact hp
    have hq' : (2 : ℝ) ^ 100 / 300 ^ 6 ≤ x / log x ^ 6 := by
      have h1 : 0 < log x ^ 6 / x := by positivity
      have := one_div_le_one_div_of_le h1 hq
      simpa [one_div_div] using this
    have : (3200 : ℝ) ≤ 1 / 1000 * (2 ^ 100 / 300 ^ 6) := by norm_num
    linarith
  have h120 : 120 * (x / log x ^ 6) - 240 / log (2 : ℝ) ^ 6 ≤ 120 * logIntegral 6 x := by
    have := mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 120)
    calc 120 * (x / log x ^ 6) - 240 / log (2 : ℝ) ^ 6
        = 120 * (x / log x ^ 6 - 2 / log 2 ^ 6) := by ring
      _ ≤ _ := this
  rw [hexp]
  linarith

end PVTwoBackend
