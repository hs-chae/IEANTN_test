/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.OpenAIQRH.v1.Conclusions
import IEANTN.Nodes.PlattTrudgian.v1.Conclusions
import IEANTN.Nodes.RosserSchoenfeld.v1.Conclusions
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! QRH supplies an alternative proof of an existing upstream source contract. -/
namespace QRHExistingRegions
open Real IEANTN

/-- Join a genuine half-plane to a separately verified RH rectangle. -/
theorem hybrid_nonzero {β T σ t : ℝ} (hβlt : β < 1)
    (hqrh : ZetaZeroFreeHalfPlane β) (hRH : RiemannHypothesisUpTo T)
    (ht : 0 < t) (hσ : β < σ ∨ ((1 / 2 : ℝ) < σ ∧ t ≤ T)) :
    riemannZeta (σ + t * Complex.I) ≠ 0 := by
  have hs1 : (σ : ℂ) + t * Complex.I ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.ofReal_re, zero_add, Complex.one_im] at hi
    linarith
  rcases hσ with hhigh | ⟨hhalf, hT⟩
  · exact hqrh _ (by simpa using hhigh) hs1
  · by_cases hhigh : β < σ
    · exact hqrh _ (by simpa using hhigh) hs1
    · intro hzero
      have hmem : ((σ : ℂ) + t * Complex.I) ∈
          zetaZeroesIn (Set.Ioo (1 / 2 : ℝ) 1) (Set.Icc 0 T) := by
        refine ⟨?_, ?_, hzero⟩
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
            Complex.ofReal_im, neg_zero, add_zero, Set.mem_Ioo]
          constructor <;> linarith
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
            Complex.ofReal_re, zero_add, Set.mem_Icc]
          exact ⟨ht.le, hT⟩
      exact hRH.false ⟨_, hmem⟩

/-- The exact original closed region, including log(t/17) and the threshold 21. -/
theorem rosser_schoenfeld (hqrh : OpenAIQRH.v1.zeta_seven_eighths)
    (hRH : PlattTrudgian.v1.rh_up_to) : RosserSchoenfeld.v1.zero_free_region := by
  intro σ t ht hσ
  have ht0 : 0 < t := by linarith
  have hratio : (21 / 17 : ℝ) ≤ t / 17 := by linarith
  have hpow : (2 : ℝ) ^ 3 ≤ (21 / 17 : ℝ) ^ 10 := by norm_num
  have hlower := log_le_log (by norm_num : (0 : ℝ) < 2 ^ 3) hpow
  rw [log_pow, log_pow] at hlower
  have hmon := log_le_log (by norm_num : (0 : ℝ) < 21 / 17) hratio
  have hden : 2 < (9.645908801 : ℝ) * log (t / 17) := by
    nlinarith [log_two_gt_d9]
  apply hybrid_nonzero (β := (7 / 8 : ℝ)) (by norm_num) hqrh hRH ht0
  by_cases h100 : 100 ≤ t
  · left
    have he : exp 1 ≤ t / 17 := by linarith [exp_one_lt_d9]
    have hlog := log_le_log (exp_pos 1) he
    rw [log_exp] at hlog
    have hinv : 1 / ((9.645908801 : ℝ) * log (t / 17)) < 1 / 8 := by
      apply one_div_lt_one_div_of_lt <;> nlinarith
    linarith
  · right
    have hinv : 1 / ((9.645908801 : ℝ) * log (t / 17)) < 1 / 2 := by
      apply one_div_lt_one_div_of_lt <;> linarith
    constructor <;> linarith

end QRHExistingRegions
