/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectKernelResidual
import PiPower
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
namespace WinnerDirectKernel
open Real Set MeasureTheory IEANTN
open DudekPlattNumerics.Calculus
set_option maxHeartbeats 0
noncomputable def psiResidual (u : ℝ) : ℝ := Chebyshev.psi (exp u)-exp u
noncomputable def primePower (x : ℝ) : ℝ := Chebyshev.psi x-Chebyshev.theta x
noncomputable def anchor (A : ℝ) : ℝ := primeCounting A-Li A-(Chebyshev.theta A-A)/log A

/-- Integrability of the actual step function is proved; no continuous-primes assumption. -/
theorem psi_log_integrable {v L : ℝ} (hv : 0<v) (hL : v≤L) :
    IntervalIntegrable (fun u : ℝ=>psiResidual u/u^2) volume v L := by
  have hp : Monotone (fun u : ℝ=>Chebyshev.psi (exp u)) := Chebyshev.psi_mono.comp exp_monotone
  have hi : IntervalIntegrable (fun u : ℝ=>Chebyshev.psi (exp u)-exp u) volume v L :=
    hp.intervalIntegrable.sub (continuous_exp.intervalIntegrable v L)
  have hc : ContinuousOn (fun u : ℝ=>(u^2)⁻¹) (uIcc v L) := by
    rw [uIcc_of_le hL]
    intro u hu
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 (hv.trans_le hu.1).ne')).continuousWithinAt
  simpa only [psiResidual,div_eq_mul_inv] using hi.mul_continuousOn hc

/-- Monotone substitution applies to the actual discontinuous Chebyshev error. -/
theorem log_substitution (R : ℝ→ℝ) {v L : ℝ} (hv : 0<v) (hL : v≤L) :
    (∫ t in exp v..exp L,R t/(t*log t^2))=(∫ u in v..L,R (exp u)/u^2) := by
  have hh:=intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a:=v) (b:=L) (f:=exp) (f':=exp) (g:=fun t=>R t/(t*log t^2)) continuous_exp.continuousOn
    (fun u _=>hasDerivAt_exp u) (fun u _=>(exp_pos u).le)
  rw [←hh]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hL] at hu
  simp only [Function.comp_apply,log_exp]
  have hu0:= (hv.trans_le hu.1).ne'
  field_simp [exp_ne_zero,hu0]

 theorem primePower_integrable {A x : ℝ} (hA : 1<A) (hAx : A≤x) :
    IntervalIntegrable (fun t=>primePower t/(t*log t^2)) volume A x := by
  have hi : IntervalIntegrable (fun t : ℝ=>(Chebyshev.psi t-Chebyshev.theta t)*(t*log t^2)⁻¹) volume A x :=
    (Chebyshev.psi_mono.intervalIntegrable.sub Chebyshev.theta_mono.intervalIntegrable).mul_continuousOn (FKS2Sol.contOn_inv_t_log_sq hA hAx)
  simpa only [primePower,div_eq_mul_inv] using hi

/-- Exact actual-prime identity before applying any absolute value to a zero kernel. -/
theorem pi_psi_identity {v L : ℝ} (hv : 2≤exp v) (hL : v≤L) :
    primeCounting (exp L)-Li (exp L)=anchor (exp v)+logResidual psiResidual v L-
      (primePower (exp L)/L+∫ t in exp v..exp L,primePower t/(t*log t^2)) := by
  have hvp : 0<v := by
    have he : 1<exp v := lt_of_lt_of_le (by norm_num) hv
    exact one_lt_exp_iff.mp he
  have hAx : exp v≤exp L := exp_le_exp.mpr hL
  have hA1 : 1<exp v := lt_of_lt_of_le (by norm_num) hv
  have hψ : IntervalIntegrable (fun t=>(Chebyshev.psi t-t)/(t*log t^2)) volume (exp v) (exp L) := by
    have hi := (Chebyshev.psi_mono.intervalIntegrable.sub
      (continuous_id.intervalIntegrable (μ:=volume) (exp v) (exp L))).mul_continuousOn (FKS2Sol.contOn_inv_t_log_sq hA1 hAx)
    simpa only [div_eq_mul_inv,id_eq] using hi
  have hP:=primePower_integrable hA1 hAx
  have hs : (∫ t in exp v..exp L,(Chebyshev.theta t-t)/(t*log t^2))=
      (∫ t in exp v..exp L,(Chebyshev.psi t-t)/(t*log t^2))-
        ∫ t in exp v..exp L,primePower t/(t*log t^2) := by
    rw [←intervalIntegral.integral_sub hψ hP]
    apply intervalIntegral.integral_congr
    intro t ht
    unfold primePower
    ring
  have hp:=FKS2Sol.piMinusLi_sub hv hAx
  rw [hs,log_substitution (fun t=>Chebyshev.psi t-t) hvp hL] at hp
  simp only [log_exp] at hp
  simp only [primePower] at hp
  unfold anchor logResidual psiResidual primePower
  simp only [log_exp]
  rw [hp]
  ring

 theorem anchor_bound {A : ℝ} (hA : 2≤A) : |anchor A|≤4*A := by
  have hp:=FKS2Sol.piMinusLi_eq hA
  have hlog2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hc : 2/log (2:ℝ)≤3 := by
    apply (div_le_iff₀ hlog2).mpr
    linarith [DudekPlattNumerics.v4.Numerics.hlog2_proof]
  have hi : |∫ t in (2:ℝ)..A,(Chebyshev.theta t-t)/(t*log t^2)|≤4*(A-2) := by
    have hh:=intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(2:ℝ)) (b:=A) (C:=(4:ℝ))
      (f:=fun t=>(Chebyshev.theta t-t)/(t*log t^2)) (fun t ht=>by
        rw [uIoc_of_le hA] at ht
        simpa only [Real.norm_eq_abs,thetaError] using
          abs_errorKernel_le_four DudekPlattNumerics.v4.Numerics.hlog2_proof ht.1.le)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hA)] using hh
  have he : anchor A=2/log 2+∫ t in (2:ℝ)..A,(Chebyshev.theta t-t)/(t*log t^2) := by
    unfold anchor
    linarith
  rw [he]
  have hh:=abs_add_le (2/log (2:ℝ)) (∫ t in (2:ℝ)..A,(Chebyshev.theta t-t)/(t*log t^2))
  rw [abs_of_nonneg (by positivity : 0≤2/log (2:ℝ))] at hh
  linarith

#print axioms psi_log_integrable
#print axioms pi_psi_identity
#print axioms anchor_bound
end WinnerDirectKernel
