import IEANTN.Nodes.FKS2Numerics.v1.Conclusions
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace FKS2Scalar

noncomputable def exactTarget : ℝ := FKS2Numerics.v1.nuAsympE30

noncomputable def sum1 : ℝ :=
  ∑ k ∈ Finset.Icc 3 43, Real.exp (30 * ((1 : ℝ) / (k : ℕ) - 1 / 3))

noncomputable def sum2 : ℝ :=
  ∑ k ∈ Finset.Icc 3 44, Real.exp ((44 * Real.log 2) * ((1 : ℝ) / (k : ℕ) - 1 / 3))

noncomputable def normalized : ℝ :=
  (1 / 121.096) * Real.sqrt (5.5666305 / 30) ^ 3 *
    Real.exp (2 * Real.sqrt (30 / 5.5666305)) *
    ((1 + 1.93378e-8) * 30 * Real.exp (-15) +
      ((1 + 1.93378e-8) * max sum1 sum2) * 30 * Real.exp (-20))

theorem floor30 : ⌊(30 : ℝ) / Real.log 2⌋₊ = 43 := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (Nat.floor_eq_iff (by positivity)).2
  constructor
  · apply (le_div_iff₀ hp).2
    norm_num only [Nat.cast_ofNat]
    nlinarith [Real.log_two_lt_d9]
  · apply (div_lt_iff₀ hp).2
    norm_num only [Nat.cast_ofNat]
    nlinarith [Real.log_two_gt_d9]

theorem floor44 : ⌊Real.log ((2 : ℝ) ^ (44 : ℕ)) / Real.log 2⌋₊ = 44 := by
  have hn : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.log_pow, mul_div_cancel_right₀ _ hn]
  norm_num

theorem f_exp30 : BKLNW.v1.f (Real.exp 30) = sum1 := by
  unfold BKLNW.v1.f sum1
  rw [Real.log_exp, floor30]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Real.exp_mul]

theorem f_pow44 : BKLNW.v1.f ((2 : ℝ) ^ (44 : ℕ)) = sum2 := by
  unfold BKLNW.v1.f sum2
  rw [floor44]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
  norm_num

theorem target_normalization : exactTarget = normalized := by
  have hp : (0 : ℝ) ≤ 5.5666305 / 30 := by norm_num
  unfold exactTarget FKS2Numerics.v1.nuAsympE30 normalized BKLNW.v1.a₂
  rw [floor30]
  rw [show (43 + 1 : ℕ) = 44 from rfl]
  rw [f_exp30, f_pow44, Real.rpow_div_two_eq_sqrt _ hp]
  rw [← Real.exp_mul, ← Real.exp_mul]
  norm_num

theorem upstream_margin_zero : IEANTN.margin 0 = 1 := by
  simp [IEANTN.margin]

end FKS2Scalar
