import SpectralGMRefined
import ActualSourceFinite
namespace RHLimit.Ram620
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan RHLimit.Spectral
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"
noncomputable def psiDeficit (z : ℝ) : ℝ := (exp z-Chebyshev.psi (exp z))/exp (z/2)
noncomputable def shift (l u : ℝ) : ℝ := (693/5000:ℝ)/(l-6)+(361/25:ℝ)*u*exp (-l/2)

lemma refined_deficit_band (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {l u z : ℝ} (hl : 12 ≤ l) (hlz : l ≤ z) (hzu : z ≤ u) :
    |riemannDeficit z-psiDeficit z| ≤ shift l u := by
  have hz : 0 < z := by linarith
  have h := actual_J_refined_GM hRH hGM hP hJ
    (show exp 12 ≤ exp z from exp_le_exp.mpr (by linarith))
  unfold refinedBound refinedLeading at h
  rw [Real.log_exp,←Real.exp_half] at h
  have hm := mul_le_mul_of_nonneg_right h (show 0 ≤ z/exp (z/2) by positivity)
  have heq : riemannDeficit z-psiDeficit z =
      -(riemannPrimeCounting (exp z)-li (exp z)-(Chebyshev.psi (exp z)-exp z)/z)*(z/exp (z/2)) := by
    unfold riemannDeficit psiDeficit
    field_simp [hz.ne',exp_ne_zero]
    ring
  rw [heq,abs_mul,abs_neg,abs_of_nonneg (show 0 ≤ z/exp (z/2) by positivity)]
  have hr : (361/25+(693/5000:ℝ)*exp (z/2)/(z*(z-6)))*(z/exp (z/2)) =
      (361/25:ℝ)*z*exp (-z/2)+(693/5000:ℝ)/(z-6) := by
    rw [show -z/2 = -(z/2) by ring,exp_neg]
    field_simp [hz.ne',show z-6 ≠ 0 by linarith,exp_ne_zero]
  change |riemannPrimeCounting (exp z)-li (exp z)-(Chebyshev.psi (exp z)-exp z)/z| * (z/exp (z/2)) ≤ _
  apply hm.trans
  change (361/25+(693/5000:ℝ)*exp (z/2)/(z*(z-6)))*(z/exp (z/2)) ≤ _
  rw [hr]
  have hd : (693/5000:ℝ)/(z-6) ≤ (693/5000:ℝ)/(l-6) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hE : exp (-z/2) ≤ exp (-l/2) := exp_le_exp.mpr (by linarith)
  -- the left factor uses the slab upper endpoint, independently of exp monotonicity
  have hM' : z*exp (-z/2) ≤ u*exp (-l/2) :=
    mul_le_mul hzu hE (exp_pos _).le (by linarith)
  unfold shift
  linarith
#print axioms refined_deficit_band
end RHLimit.Ram620
