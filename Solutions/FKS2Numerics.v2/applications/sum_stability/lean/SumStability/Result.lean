import SumStability.Examples
import Mathlib.Basic.Real.Basic

namespace SumStability

/-- Exact sum of the represented input values, regarded as a real number. -/
def exactSum (xs : List ℚ) : ℝ := (xs.sum : ℚ)

def sumAbs (xs : List ℚ) : ℝ := ((xs.map abs).sum : ℚ)

theorem exactSum_as_sum (xs : List ℚ) : exactSum xs = (xs.map (fun x => (x : ℝ))).sum := by
  induction xs with
  | nil => simp [exactSum]
  | cons x xs ih => simpa [exactSum, Rat.cast_add] using congrArg ((x : ℝ) + ·) ih

theorem sumAbs_as_sum (xs : List ℚ) :
    sumAbs xs = (xs.map (fun x => |(x : ℝ)|)).sum := by
  induction xs with
  | nil => simp [sumAbs]
  | cons x xs ih => simpa [sumAbs, Rat.cast_add, Rat.cast_abs] using congrArg (|(x : ℝ)| + ·) ih

/-- Public real-valued endpoint; all values, output, and both C states are universally quantified. -/
theorem c_sum_forward_error_real (xs : List ℚ) (initial final : CState) (out : ℚ)
    (hn : 1 ≤ xs.length ∧ xs.length ≤ 64) (hdomain : ValidInputs xs)
    (hrep : RepresentsInput initial xs) (hexec : ExecC selectedSumProgram initial final out) :
    |(out : ℝ) - exactSum xs| ≤ (gamma (xs.length - 1) : ℝ) * sumAbs xs := by
  have h := c_sum_forward_error xs initial final out hn hdomain hrep hexec
  dsimp [exactSum, sumAbs]
  exact_mod_cast h

/-- The checked actual file and the error conclusion, without an extra source-check hypothesis. -/
theorem source_and_forward_error (xs : List ℚ) (initial final : CState) (out : ℚ)
    (hn : 1 ≤ xs.length ∧ xs.length ≤ 64) (hdomain : ValidInputs xs)
    (hrep : RepresentsInput initial xs) (hexec : ExecC selectedSumProgram initial final out) :
    SourceCorresponds selectedSource selectedSumProgram ∧
    |(out : ℝ) - exactSum xs| ≤ (gamma (xs.length - 1) : ℝ) * sumAbs xs :=
  ⟨selected_source_checked, c_sum_forward_error_real xs initial final out hn hdomain hrep hexec⟩

/-- Supported exact arguments lie far inside the binary64 normal/finite range. -/
theorem supported_normal_range {x : ℚ} (hl : low ≤ x) (hh : x ≤ 128) :
    (2 : ℚ) ^ (-1022 : ℤ) ≤ x ∧ x < ((2 : ℚ) ^ 53 - 1) * 2 ^ (971 : ℕ) := by
  constructor
  · have hp : (2 : ℚ) ^ (-1022 : ℤ) ≤ (2 : ℚ) ^ (-40 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by norm_num)
    exact le_trans (by simpa [low] using hp) hl
  · have hp : (1 : ℚ) ≤ 2 ^ (971 : ℕ) := one_le_pow₀ (by norm_num)
    have hm : (128 : ℚ) < (2 : ℚ) ^ 53 - 1 := by norm_num
    have hmpos : (0 : ℚ) ≤ (2 : ℚ) ^ 53 - 1 := by norm_num
    have hb := mul_le_mul_of_nonneg_left hp hmpos
    exact lt_of_le_of_lt hh (lt_of_lt_of_le hm (by simpa only [mul_one] using hb))

theorem c_sum_finite_normal (xs : List ℚ) (initial final : CState) (out : ℚ)
    (hn : 1 ≤ xs.length ∧ xs.length ≤ 64) (hdomain : ValidInputs xs)
    (hrep : RepresentsInput initial xs) (hexec : ExecC selectedSumProgram initial final out) :
    Binary64 out ∧ low ≤ out ∧ out ≤ 128 ∧
      (2 : ℚ) ^ (-1022 : ℤ) ≤ out := by
  obtain ⟨_, last, hloop, hfinal, hout⟩ := hexec
  have hh := for_exec_accum hloop xs (initialized_rep hrep) hn.2 (by simp [initialized])
    (by simpa [initialized] using Accum.zero)
  have hne : xs ≠ [] := by intro h; simp [h] at hn
  obtain ⟨hl, hh, hf, _⟩ := (accum_invariant hh.1 hdomain hn.2).2 hne
  have hlen : (xs.length : ℚ) ≤ 64 := by exact_mod_cast hn.2
  rw [hout]
  exact ⟨hf, hl, by linarith, (supported_normal_range hl (by linarith)).1⟩

end SumStability
