/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PsiSmoothing

/-! The improved box consumer uses the analytically exact first absolute Mellin
moment and a4096-log-term certificate for the second moment. Their exact
mathematical contracts remain visible inputs; no numerical output is asserted
as an axiom or evaluated with a native execution fact. -/
namespace PsiBoxExact
open Real PsiSmoothing

theorem psi_series (rh : RiemannHypothesis)
    (hef : AveragedExplicitFormula box) (hz : ZeroDensityMomentEstimate box)
    (hm : MainTermEstimate box) (ht : TrivialTermEstimate box)
    (h0 : J box 0 = Real.log 2) (h1 : J box 1 ≤ 71 / 100) :
    ∀ x : ℝ, Real.exp 35 ≤ x → |Chebyshev.psi x - x| ≤
      Real.sqrt x * envelope (Real.log 2) (71 / 100) (Real.log x) := by
  intro x hx
  have hx0 : 0 < x := (Real.exp_pos 35).trans_le hx
  have hlog : 35 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 35) hx
    simpa only [Real.log_exp] using h
  have h := psi_from_smoothing box box_continuous box_nonneg box_mass
    rh hef hz hm ht (le_of_eq h0) h1 (Real.log x) hlog
  simpa only [Real.exp_log hx0] using h

/-- The128-log convex-trapezoid moment cap, stronger than the4096-log fallback. -/
theorem psi_fast (rh : RiemannHypothesis)
    (hef : AveragedExplicitFormula box) (hz : ZeroDensityMomentEstimate box)
    (hm : MainTermEstimate box) (ht : TrivialTermEstimate box)
    (h0 : J box 0 = Real.log 2) (h1 : J box 1 ≤ 567 / 800) :
    ∀ x : ℝ, Real.exp 35 ≤ x → |Chebyshev.psi x - x| ≤
      Real.sqrt x * envelope (Real.log 2) (567 / 800) (Real.log x) := by
  intro x hx
  have hx0 : 0 < x := (Real.exp_pos 35).trans_le hx
  have hlog : 35 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 35) hx
    simpa only [Real.log_exp] using h
  have h := psi_from_smoothing box box_continuous box_nonneg box_mass
    rh hef hz hm ht (le_of_eq h0) h1 (Real.log x) hlog
  simpa only [Real.exp_log hx0] using h

/-- The entire new full envelope improves the rounded quadrature box by>.046. -/
theorem improves_rounded_box {L : ℝ} (hL : 35 ≤ L) :
    46 / 1000 < envelope (701 / 1000) (3 / 4) L -
      envelope (Real.log 2) (71 / 100) L := by
  have hv := v_gt_135 hL
  have hlog := Real.log_two_lt_d9
  have heq : envelope (701 / 1000) (3 / 4) L -
      envelope (Real.log 2) (71 / 100) L =
      (((701 / 500 : ℝ) - 2 * Real.log 2) * v L + 2 / 25) /
        (2 * Real.pi) := by
    unfold envelope
    ring
  rw [heq]
  apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  nlinarith [Real.pi_lt_d2]

/-- A kernel-checked uniform strict comparison of the complete functions. -/
theorem improves_B5 {L : ℝ} (hL : 35 ≤ L) :
    546 / 1000 < envelope (831 / 1000) (287 / 500) L -
      envelope (Real.log 2) (71 / 100) L := by
  have h5 := box_improves_B5 hL
  have hb := improves_rounded_box hL
  linarith

theorem fast_improves_B5 {L : ℝ} (hL : 35 ≤ L) :
    546 / 1000 < envelope (831 / 1000) (287 / 500) L -
      envelope (Real.log 2) (567 / 800) L := by
  have h := improves_B5 hL
  have he : envelope (Real.log 2) (567 / 800) L ≤
      envelope (Real.log 2) (71 / 100) L := by
    unfold envelope
    have hp : 0 < 2 * Real.pi := by positivity
    apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_right _ hp.le
    linarith
  linarith

#print axioms psi_fast
#print axioms fast_improves_B5

#print axioms psi_series
#print axioms improves_B5
end PsiBoxExact
