/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Correction.Enclosure

namespace FKS2Correction
open FKS2Scalar SumStability
open FKS2SumBridge (specError1 specError2)

def acc1 : ℚ := (get baselineFrame.env "s1").getD 0
def acc2 : ℚ := (get baselineFrame.env "s2").getD 0

theorem baseline_sum_errors :
    |(acc1 : ℝ) - FKS2Scalar.sum1| ≤ (specError1 : ℝ) ∧
    |(acc2 : ℝ) - FKS2Scalar.sum2| ≤ (specError2 : ℝ) := by
  unfold acc1 acc2
  rw [baseline_prefix_execution.2.2.1, baseline_prefix_execution.2.2.2]
  exact FKS2SumBridge.rational_specification_errors


/-- Actual rounded suffix constants read from the existing source execution. -/
def prefactor : ℚ := (get baselineFrame.env "p").getD 0
def constantB : ℚ := (get baselineFrame.env "b1").getD 0
def sumCoefficient : ℚ :=
  (get baselineFrame.env "a1").getD 0 * 300 * (get baselineFrame.env "e200").getD 0

def hybridRat (a b : ℚ) : ℚ := prefactor * (constantB + sumCoefficient * max a b)
noncomputable def hybrid (a b : ℝ) : ℝ :=
  (prefactor : ℝ) * ((constantB : ℝ) + (sumCoefficient : ℝ) * max a b)

def hybridLo : ℚ := hybridRat s1lo s2lo
def hybridHi : ℚ := hybridRat s1hi s2hi
def comparisonLo : ℚ := min nuLo hybridLo
def comparisonHi : ℚ := max nuHi hybridHi

def coefficientError : ℚ := 1 / 10 ^ 69
def suffixError : ℚ := 1 / 10 ^ 74
def sensitivity : ℚ := prefactor * sumCoefficient

def totalError : ℚ :=
  coefficientError + suffixError + sensitivity * max specError1 specError2

/-- Only rational finite source-linked arithmetic and certified interval comparisons.
No Real.exp oracle, old whole-program error, or direct rational sum-roundoff certificate. -/
theorem composition_checks :
    0 < prefactor ∧ 0 < sumCoefficient ∧
    |baselineQ - hybridRat acc1 acc2| ≤ suffixError ∧
    comparisonHi - comparisonLo ≤ coefficientError ∧
    0 ≤ specError1 ∧ 0 ≤ specError2 ∧ 0 ≤ totalError ∧
    totalError ≤ 1 / 10 ^ 68 ∧ baselineQ + totalError ≤ 11 / 10 ^ 62 := by
  native_decide

theorem hybrid_rat_eq (a b : ℚ) : hybrid (a : ℝ) (b : ℝ) = (hybridRat a b : ℝ) := by
  simp [hybrid, hybridRat]

theorem hybrid_mono {a b A B : ℝ} (ha : a ≤ A) (hb : b ≤ B) : hybrid a b ≤ hybrid A B := by
  have hp : (0 : ℝ) ≤ (prefactor : ℝ) := by exact_mod_cast composition_checks.1.le
  have hc : (0 : ℝ) ≤ (sumCoefficient : ℝ) := by exact_mod_cast composition_checks.2.1.le
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (max_le_max ha hb) hc)) hp

theorem exact_hybrid_enclosure :
    (hybridLo : ℝ) ≤ hybrid FKS2Scalar.sum1 FKS2Scalar.sum2 ∧
    hybrid FKS2Scalar.sum1 FKS2Scalar.sum2 ≤ (hybridHi : ℝ) := by
  rw [hybridLo, hybridHi, ← hybrid_rat_eq, ← hybrid_rat_eq]
  exact ⟨hybrid_mono sum1_bounds.1 sum2_bounds.1, hybrid_mono sum1_bounds.2 sum2_bounds.2⟩

theorem coefficient_error :
    |hybrid FKS2Scalar.sum1 FKS2Scalar.sum2 - FKS2Numerics.v3.nuStar 121.096 300| ≤ (coefficientError : ℝ) := by
  have ht := target_enclosure
  have hg := exact_hybrid_enclosure
  have hl1 : (comparisonLo : ℝ) ≤ (nuLo : ℝ) := by exact_mod_cast min_le_left nuLo hybridLo
  have hl2 : (comparisonLo : ℝ) ≤ (hybridLo : ℝ) := by exact_mod_cast min_le_right nuLo hybridLo
  have hh1 : (nuHi : ℝ) ≤ (comparisonHi : ℝ) := by exact_mod_cast le_max_left nuHi hybridHi
  have hh2 : (hybridHi : ℝ) ≤ (comparisonHi : ℝ) := by exact_mod_cast le_max_right nuHi hybridHi
  have hw : (comparisonHi : ℝ) - (comparisonLo : ℝ) ≤ (coefficientError : ℝ) := by
    exact_mod_cast composition_checks.2.2.2.1
  rw [abs_le]
  constructor <;> linarith [hl1.trans ht.1, hl2.trans hg.1, ht.2.trans hh1, hg.2.trans hh2]

/-- Nonzero source-derived sensitivity propagates the newly proved generic sum errors. -/
theorem hybrid_sum_error :
    |hybrid (acc1 : ℝ) (acc2 : ℝ) - hybrid FKS2Scalar.sum1 FKS2Scalar.sum2| ≤
      (sensitivity * max specError1 specError2 : ℝ) := by
  have hc : (0 : ℝ) ≤ (sensitivity : ℝ) := by
    have hp : 0 ≤ sensitivity := mul_nonneg composition_checks.1.le composition_checks.2.1.le
    exact_mod_cast hp
  have hmax := (abs_max_sub_max_le_max (acc1 : ℝ) (acc2 : ℝ)
    FKS2Scalar.sum1 FKS2Scalar.sum2).trans
    (max_le_max baseline_sum_errors.1 baseline_sum_errors.2)
  have he : hybrid (acc1 : ℝ) (acc2 : ℝ) - hybrid FKS2Scalar.sum1 FKS2Scalar.sum2 =
      (sensitivity : ℝ) * (max (acc1 : ℝ) (acc2 : ℝ) - max FKS2Scalar.sum1 FKS2Scalar.sum2) := by
    simp only [hybrid, sensitivity, Rat.cast_mul]
    ring
  rw [he, abs_mul, abs_of_nonneg hc]
  simpa using mul_le_mul_of_nonneg_left hmax hc

theorem baseline_whole_error :
    |(baselineQ : ℝ) - FKS2Numerics.v3.nuStar 121.096 300| ≤ (totalError : ℝ) := by
  have hs : |(baselineQ : ℝ) - hybrid (acc1 : ℝ) (acc2 : ℝ)| ≤ (suffixError : ℝ) := by
    rw [hybrid_rat_eq]
    exact_mod_cast composition_checks.2.2.1
  change |(baselineQ : ℝ) - FKS2Numerics.v3.nuStar 121.096 300| ≤ _
  calc
    _ ≤ |(baselineQ : ℝ) - hybrid (acc1 : ℝ) (acc2 : ℝ)| +
        |hybrid (acc1 : ℝ) (acc2 : ℝ) - FKS2Numerics.v3.nuStar 121.096 300| := abs_sub_le _ _ _
    _ ≤ (suffixError : ℝ) + (|hybrid (acc1 : ℝ) (acc2 : ℝ) -
        hybrid FKS2Scalar.sum1 FKS2Scalar.sum2| +
        |hybrid FKS2Scalar.sum1 FKS2Scalar.sum2 - FKS2Numerics.v3.nuStar 121.096 300|) :=
      add_le_add hs (abs_sub_le _ _ _)
    _ ≤ (suffixError : ℝ) + ((sensitivity * max specError1 specError2 : ℝ) +
        (coefficientError : ℝ)) :=
      add_le_add le_rfl (add_le_add hybrid_sum_error coefficient_error)
    _ = _ := by simp [totalError]; ring

/-- Successful original source execution implies the new stability-derived error bound. -/
theorem baseline_source_error {out : Rat}
    (hRun : FKS2Scalar.ExecC baselineProgram out) :
    |(out : ℝ) - FKS2Numerics.v3.nuStar 121.096 300| ≤ (totalError : ℝ) := by
  have ho : out = baselineQ := Option.some.inj (hRun.symm.trans baseline_source_execution)
  rw [ho]
  exact baseline_whole_error

theorem baseline_error_witness :
    ∃ out : Rat, FKS2Scalar.ExecC baselineProgram out ∧
      |(out : ℝ) - FKS2Numerics.v3.nuStar 121.096 300| ≤ (totalError : ℝ) := by
  exact ⟨baselineQ, baseline_source_execution, baseline_source_error baseline_source_execution⟩

theorem baseline_provider :
    FKS2Numerics.v3.nuStar 121.096 300 ≤ ((11 : ℚ) / 10 ^ 62 : ℝ) := by
  have h := (abs_le.mp baseline_whole_error).1
  have hb : (baselineQ : ℝ) + (totalError : ℝ) ≤ ((11 : ℚ) / 10 ^ 62 : ℝ) := by
    exact_mod_cast composition_checks.2.2.2.2.2.2.2.2
  linarith


end FKS2Correction
