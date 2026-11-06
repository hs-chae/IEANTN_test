/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.CotangentSeries.v1.Conclusions
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

open Complex Real Set Filter
open scoped Topology

namespace CotangentSeriesSolution

noncomputable def term (z : ℂ) (n m : ℕ) : ℂ :=
  (2 * z / (m + 1 : ℂ) ^ 2) * (z ^ 2 / (m + 1 : ℂ) ^ 2) ^ n

lemma integer_complement {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    z ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨k, hk⟩
  have hi : |k| < (1 : ℤ) := by
    have hr : |(k : ℝ)| < 1 := by simpa only [← hk, Complex.norm_intCast] using hz
    exact_mod_cast hr
  have hk0 : k = 0 := Int.abs_lt_one_iff.mp hi
  subst k
  exact hz0 (by simpa using hk.symm)

lemma ratio_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖z ^ 2 / (m + 1 : ℂ) ^ 2‖ < 1 := by
  have ha : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have ha2 : (1 : ℝ) ≤ (m + 1 : ℕ) ^ 2 := by nlinarith
  have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  simp only [norm_div, norm_pow, show (m + 1 : ℂ) = ((m + 1 : ℕ) : ℂ) by push_cast; rfl,
    Complex.norm_natCast]
  exact (div_le_self (by positivity : 0 ≤ ‖z‖ ^ 2) ha2).trans_lt hz2

lemma norm_term_bound {z : ℂ} (n m : ℕ) :
    ‖term z n m‖ ≤
      (2 * ‖z‖ * (‖z‖ ^ 2) ^ n) * (1 / (m + 1 : ℝ) ^ 2) := by
  have ha : (1 : ℝ) ≤ m + 1 := by linarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
  have ha2 : (1 : ℝ) ≤ (m + 1 : ℝ) ^ 2 := by nlinarith
  have hratio : ‖z‖ ^ 2 / (m + 1 : ℝ) ^ 2 ≤ ‖z‖ ^ 2 :=
    div_le_self (by positivity) ha2
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ ‖z‖ ^ 2 / (m + 1 : ℝ) ^ 2) hratio n
  unfold term
  have hn : ‖(m + 1 : ℂ)‖ = (m + 1 : ℝ) := by
    rw [show (m + 1 : ℂ) = ((m + 1 : ℕ) : ℂ) by push_cast; rfl,
      Complex.norm_natCast]
    push_cast
    rfl
  simp only [norm_mul, norm_div, norm_pow, hn, Complex.norm_ofNat]
  calc
    _ ≤ (2 * ‖z‖ / (m + 1 : ℝ) ^ 2) * (‖z‖ ^ 2) ^ n :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

lemma double_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (Function.uncurry (term z)) := by
  have hz2 : ‖‖z‖ ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [norm_nonneg z]
  have hg := (summable_geometric_of_norm_lt_one hz2).mul_left (2 * ‖z‖)
  have hp : Summable (fun m : ℕ ↦ 1 / (m + 1 : ℝ) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr
      (summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hb := hg.mul_of_nonneg hp (fun _ ↦ by positivity) (fun _ ↦ by positivity)
  exact hb.of_norm_bounded (fun q ↦ norm_term_bound q.1 q.2)

lemma term_nat_power (z : ℂ) (n m : ℕ) :
    term z n m = 2 * (1 / (m + 1 : ℂ) ^ (2 * n + 2)) * z ^ (2 * n + 1) := by
  unfold term
  rw [div_pow, ← pow_mul, ← pow_mul]
  simp only [pow_add, pow_one]
  field_simp
  <;> ring

lemma sum_over_m (z : ℂ) (n : ℕ) :
    (∑' m : ℕ, term z n m) = 2 * riemannZeta (2 * (n : ℂ) + 2) * z ^ (2 * n + 1) := by
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow
    (s := ((2 * n + 2 : ℕ) : ℂ)) (by
      simp only [Complex.natCast_re]
      exact_mod_cast (show 1 < 2 * n + 2 by omega))
  simp only [Complex.cpow_natCast] at hz
  have he : ((2 * n + 2 : ℕ) : ℂ) = 2 * (n : ℂ) + 2 := by push_cast; rfl
  calc
    _ = ∑' m : ℕ, 2 * (1 / (m + 1 : ℂ) ^ (2 * n + 2)) * z ^ (2 * n + 1) :=
      tsum_congr (fun m ↦ term_nat_power z n m)
    _ = (2 * ∑' m : ℕ, 1 / (m + 1 : ℂ) ^ (2 * n + 2)) * z ^ (2 * n + 1) := by
      rw [tsum_mul_right, tsum_mul_left]
    _ = _ := by rw [← hz, he]

lemma sum_over_n {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    (∑' n : ℕ, term z n m) = 2 * z / ((m + 1 : ℂ) ^ 2 - z ^ 2) := by
  have hm : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  have hratio := ratio_norm_lt_one hz m
  have hgeom := (hasSum_geometric_of_norm_lt_one hratio).mul_left
    (2 * z / (m + 1 : ℂ) ^ 2)
  change HasSum (term z · m) _ at hgeom
  rw [hgeom.tsum_eq]
  have hq : z ^ 2 / (m + 1 : ℂ) ^ 2 ≠ 1 := by
    intro he
    rw [he, norm_one] at hratio
    exact lt_irrefl 1 hratio
  have hr : 1 - z ^ 2 / (m + 1 : ℂ) ^ 2 ≠ 0 := sub_ne_zero.mpr hq.symm
  have hd : (m + 1 : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
    intro he
    apply hr
    rw [← sub_eq_zero.mp he, div_self (pow_ne_zero 2 hm)]
    ring
  field_simp
  <;> ring

lemma geometric_eq_neg_cotTerm {z : ℂ} (h : z ∈ Complex.integerComplement) (m : ℕ) :
    2 * z / ((m + 1 : ℂ) ^ 2 - z ^ 2) = -cotTerm z m := by
  have hp : z + (m + 1 : ℂ) ≠ 0 := by
    simpa using Complex.integerComplement_add_ne_zero h ((m : ℤ) + 1)
  have hm : z - (m + 1 : ℂ) ≠ 0 := by
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      ← sub_eq_add_neg] using Complex.integerComplement_add_ne_zero h (-((m : ℤ) + 1))
  have hd : (m + 1 : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
    rw [show (m + 1 : ℂ) ^ 2 - z ^ 2 = -(z + (m + 1)) * (z - (m + 1)) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr hp) hm
  rw [cotTerm_identity h m]
  field_simp
  <;> ring

/-- The exact unchanged network predicate, obtained by absolutely summing the
geometric expansions of Mathlib's paired cotangent partial fractions. -/
theorem cot_series_zeta_values : CotangentSeries.v1.cot_series_zeta_values := by
  intro z hz0 hz
  have hInt := integer_complement hz0 hz
  have hab := double_summable hz
  have hsum := hab.prod.hasSum
  have hval : (∑' n : ℕ, ∑' m : ℕ, term z n m) =
      1 / z - (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) := by
    calc
      _ = ∑' m : ℕ, ∑' n : ℕ, term z n m := hab.tsum_comm.symm
      _ = ∑' m : ℕ, -cotTerm z m := by
        apply tsum_congr
        intro m
        exact (sum_over_n hz m).trans (geometric_eq_neg_cotTerm hInt m)
      _ = -(∑' m : ℕ, cotTerm z m) := tsum_neg
      _ = _ := by
        simp only [cotTerm]
        rw [← cot_series_rep' hInt]
        ring
  have hf : (fun n : ℕ ↦ ∑' m : ℕ, term z n m) =
      (fun n : ℕ ↦ 2 * riemannZeta (2 * (n : ℂ) + 2) * z ^ (2 * n + 1)) := by
    funext n
    exact sum_over_m z n
  change HasSum (fun n : ℕ ↦ ∑' m : ℕ, term z n m)
    (∑' n : ℕ, ∑' m : ℕ, term z n m) at hsum
  rw [hval, hf] at hsum
  exact hsum

end CotangentSeriesSolution

#print axioms CotangentSeriesSolution.cot_series_zeta_values
