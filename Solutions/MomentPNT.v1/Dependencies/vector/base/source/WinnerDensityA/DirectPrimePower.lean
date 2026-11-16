/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectActualPi
namespace WinnerDirectKernel
open Real Set MeasureTheory IEANTN
set_option maxHeartbeats 0

theorem primePower_exp_bound {u : ℝ} (hu : 2≤u) :
    |primePower (exp u)|≤exp (u/2)*u^2 := by
  have hu0 : 0<u := by linarith
  have hx : 1≤exp u := one_le_exp_iff.mpr hu0.le
  have hp:=Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
  rw [←exp_half,log_exp] at hp
  unfold primePower
  have hh : 2*exp (u/2)*u≤exp (u/2)*u^2 := by
    have hu2 : 2*u≤u^2 := by nlinarith
    have hm:=mul_le_mul_of_nonneg_left hu2 (exp_pos (u/2)).le
    nlinarith
  exact hp.trans hh

theorem primePower_correction {v L : ℝ} (hv : 2≤v) (hL : v≤L) :
    |primePower (exp L)/L+∫ t in exp v..exp L,primePower t/(t*log t^2)|≤
      (L+2)*exp (L/2) := by
  have hv0 : 0<v := by linarith
  have hLp : 0<L := hv0.trans_le hL
  have hpoint : ∀ u∈Ioc v L, ‖primePower (exp u)/u^2‖≤exp (u/2) := by
    intro u hu
    have hu2 : 2≤u := hv.trans hu.1.le
    have hup : 0<u := by linarith
    rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (sq_nonneg u)]
    apply (div_le_iff₀ (pow_pos hup 2)).mpr
    exact primePower_exp_bound hu2
  have hi : IntervalIntegrable (fun u : ℝ=>exp (u/2)) volume v L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hb:=intervalIntegral.norm_integral_le_of_norm_le hL (Filter.Eventually.of_forall hpoint) hi
  rw [Real.norm_eq_abs] at hb
  have he : (∫ u in v..L,exp (u/2))≤2*exp (L/2) := by
    calc
      _ = ∫ u in v..L,exp ((1/2:ℝ)*u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        congr 1
        ring
      _ ≤ exp ((1/2:ℝ)*L)/(1/2) := integral_exp_upper (by norm_num)
      _ = _ := by
        have hx : exp ((1/2:ℝ)*L)=exp (L/2) := by congr 1;ring
        rw [hx]
        ring
  have hEnd : |primePower (exp L)/L|≤exp (L/2)*L := by
    rw [abs_div,abs_of_pos hLp]
    apply (div_le_iff₀ hLp).mpr
    convert! primePower_exp_bound (hv.trans hL) using 1 <;> ring
  rw [log_substitution primePower hv0 hL]
  have ht:=abs_add_le (primePower (exp L)/L) (∫ u in v..L,primePower (exp u)/u^2)
  nlinarith

/-- Actual Li2-normalized prime error in terms of the integrated psi residual.
All anchor, prime-power, logarithmic substitution, and convergence steps are proved. -/
theorem actual_pi_from_logResidual {v L : ℝ} (hv : 2≤v) (hL : v≤L) :
    |primeCounting (exp L)-Li (exp L)|≤
      |logResidual psiResidual v L|+4*exp v+(L+2)*exp (L/2) := by
  have hA : 2≤exp v := by linarith [add_one_le_exp v]
  rw [pi_psi_identity hA hL]
  have h1:=abs_sub (anchor (exp v)+logResidual psiResidual v L)
    (primePower (exp L)/L+∫ t in exp v..exp L,primePower t/(t*log t^2))
  have h2:=abs_add_le (anchor (exp v)) (logResidual psiResidual v L)
  have h3:=anchor_bound hA
  have h4:=primePower_correction hv hL
  linarith

 theorem actual_Epi_from_logResidual {v L : ℝ} (hv : 2≤v) (hL : v≤L) :
    Eπ (exp L)≤(L/exp L)*
      (|logResidual psiResidual v L|+4*exp v+(L+2)*exp (L/2)) := by
  have hLp : 0<L := by linarith
  have hh:=mul_le_mul_of_nonneg_left (actual_pi_from_logResidual hv hL)
    (by positivity : 0≤L/exp L)
  convert! hh using 1
  unfold Eπ
  rw [log_exp]
  field_simp
#print axioms primePower_correction
#print axioms actual_pi_from_logResidual
#print axioms actual_Epi_from_logResidual
end WinnerDirectKernel
