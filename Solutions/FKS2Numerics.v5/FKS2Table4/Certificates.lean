/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Table4.Inputs

namespace FKS2Table4
open Real FKS2Scalar

def exponent (j : ℕ) : ℚ := (7*(300+j)/8-330)/4
def cellHi (j : ℕ) : ℚ := (330*(expHi 1-1)/283)*expHi (exponent j)^4
def q300Hi : ℚ := 300^2/283*(expHi (-18.75))^2
def q330Hi : ℚ := 330^2/283*(expHi (-10.3125))^4
def anchorHi : ℚ := (330/300)*(expHi (-15))^2*(1.6997e-12+q300Hi)

theorem analytic_checks :
    expCheck 1 (expLo 1) (expHi 1) = true ∧
    expCheck (-18.75) (expLo (-18.75)) (expHi (-18.75)) = true ∧
    expCheck (-10.3125) (expLo (-10.3125)) (expHi (-10.3125)) = true ∧
    expCheck (-15) (expLo (-15)) (expHi (-15)) = true ∧
    ∀ j ∈ Finset.range 30, expCheck (exponent j) (expLo (exponent j))
      (expHi (exponent j)) = true := by native_decide

theorem input_certificate :
    inputValues.length = 30 ∧ scale = 1/(2:ℚ)^58 ∧
    (∀ s ∈ arrayLiterals++[scaleLiteral,anchorLiteral,pointLiteral,tailLiteral],
      ∃ q, decimal s = some q ∧ round64 q = some q) ∧
    (∀ j ∈ Finset.range 30, (2:ℚ)^58*cellHi j ≤ inputValues[j]!) ∧
    anchorHi ≤ anchorUpper ∧ q330Hi ≤ pointUpper ∧ q330Hi/328 ≤ tailUpper ∧
    0 ≤ expHi 1-1 := by native_decide

theorem exp_pow_upper {a : ℚ} {n : ℕ}
    (hc : expCheck a (expLo a) (expHi a) = true) :
    exp ((n:ℝ)*(a:ℝ)) ≤ ((expHi a)^n:ℚ) := by
  rw [exp_nat_mul]
  have he := (expCheck_sound hc).2
  simpa only [Rat.cast_pow] using pow_le_pow_left₀ (exp_nonneg _) he n

theorem cell_upper (j : ℕ) (hj : j ∈ Finset.range 30) :
    cell (300+j) ≤ (cellHi j:ℝ) := by
  rw [cell_normalization (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])]
  have he := (expCheck_sound analytic_checks.1).2
  norm_num only [Rat.cast_one] at he
  have hq := exp_pow_upper (n := 4) (analytic_checks.2.2.2.2 j hj)
  have hid : (4:ℝ)*(exponent j:ℝ) = 7*(300+(j:ℝ))/8-330 := by
    simp [exponent];ring
  norm_num only [Nat.cast_ofNat] at hq
  rw [hid] at hq
  push_cast at hq
  unfold cellHi
  push_cast
  exact mul_le_mul (by nlinarith) hq (exp_pos _).le
    (by
      have hn : (0:ℝ) ≤ (expHi 1:ℝ)-1 := by exact_mod_cast input_certificate.2.2.2.2.2.2.2
      positivity)

theorem q300_upper : Q 300 ≤ (q300Hi:ℝ) := by
  have h := exp_pow_upper (n := 2) analytic_checks.2.1
  norm_num at h
  unfold Q q300Hi
  push_cast
  norm_num
  nlinarith

theorem q330_upper : Q 330 ≤ (q330Hi:ℝ) := by
  have h := exp_pow_upper (n := 4) analytic_checks.2.2.1
  norm_num at h
  unfold Q q330Hi
  push_cast
  norm_num
  nlinarith

theorem anchor_upper : anchor ≤ (anchorUpper:ℝ) := by
  have he := exp_pow_upper (n := 2) analytic_checks.2.2.2.1
  norm_num at he
  have hp : 0 ≤ (expHi (-15):ℝ)^2 := sq_nonneg _
  have hQ := Q_nonneg 300
  have hbound : anchor ≤ (anchorHi:ℝ) := by
    unfold anchor anchorHi
    push_cast
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left he (by norm_num)
    · exact add_le_add_right q300_upper _
    · linarith
    · positivity
  exact hbound.trans (by exact_mod_cast input_certificate.2.2.2.2.1)

theorem point_upper : Q 330 ≤ (pointUpper:ℝ) :=
  q330_upper.trans (by exact_mod_cast input_certificate.2.2.2.2.2.1)

theorem tail_upper : Q 330/328 ≤ (tailUpper:ℝ) := by
  have h := div_le_div_of_nonneg_right q330_upper (by norm_num : (0:ℝ) ≤ 328)
  exact h.trans (by exact_mod_cast input_certificate.2.2.2.2.2.2.1)

/-- All30whole-cell mathematical contributions are bounded by the actual loaded array. -/
theorem scaled_cells_upper :
    cells ≤ (scale:ℝ)*(inputValues.sum:ℚ) := by
  have heq : inputValues.sum = ∑ j ∈ Finset.range 30,inputValues[j]! := by
    native_decide
  rw [heq, Rat.cast_sum, Finset.mul_sum]
  unfold cells
  apply Finset.sum_le_sum
  intro j hj
  have hr := input_certificate.2.2.2.1 j hj
  have hc := cell_upper j hj
  have hs := input_certificate.2.1
  rw [hs]
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
  have hrc : (2:ℝ)^58*(cellHi j:ℝ) ≤ (inputValues[j]!:ℝ) := by exact_mod_cast hr
  nlinarith

end FKS2Table4
