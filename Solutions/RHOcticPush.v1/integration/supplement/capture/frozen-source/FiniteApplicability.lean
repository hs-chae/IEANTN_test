import IEANTN.Vocabulary.RHOcticEvolution
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! An actual active-envelope comparison, not an optimality claim.
The finite Büthe 0.94 allowance dominates this Box component on their overlap. -/
namespace RHOcticPush.Applicability
open Real

lemma log_le_half {L : ℝ} (hL : 0 < L) : log L ≤ L / 2 := by
  have h := log_le_sub_one_of_pos (div_pos hL (by norm_num : (0 : ℝ) < 2))
  rw [log_div hL.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
  have hl : log (2 : ℝ) ≤ 1 := by
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Strictly improving an inactive Box component need not improve the finite
minimum used by the existing first-Mertens argument. This is a whole-ray function
comparison, independent of RH or the unresolved Box predicates. -/
theorem buthe_smaller_than_box {L : ℝ} (hL : 35 ≤ L) :
    (94 / 100 : ℝ) < IEANTN.RHOcticEvolution.boxBound L := by
  have hv : 0 ≤ L / 2 - log L := by linarith [log_le_half (by linarith : 0 < L)]
  have hlog2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have hnum : L ≤ (L / 2 - log L) ^ 2 +
      2 * log 2 * (L / 2 - log L) + 2 * (70871 / 100000) + L := by
    nlinarith [sq_nonneg (L / 2 - log L), mul_nonneg hlog2 hv]
  have hsmall : (4 / 5 : ℝ) * (2 * Real.pi) < L := by nlinarith [pi_lt_four]
  have hdiv : (4 / 5 : ℝ) <
      ((L / 2 - log L) ^ 2 + 2 * log 2 * (L / 2 - log L) +
        2 * (70871 / 100000) + L) / (2 * Real.pi) :=
    (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr (hsmall.trans_le hnum)
  unfold IEANTN.RHOcticEvolution.boxBound IEANTN.RHSmoothing.envelope
    IEANTN.RHSmoothing.v
  linarith

#print axioms buthe_smaller_than_box
end RHOcticPush.Applicability
