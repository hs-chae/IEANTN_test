import SynergyAnalytic.PairedEnvelope
namespace SynergyAnalytic
open Real Set MeasureTheory
set_option maxHeartbeats 0

theorem pairedFunctional_add {f g:ℝ→ℝ} (hf:Continuous f) (hg:Continuous g)
    (beta r L:ℝ) :
    pairedFunctional beta r L (fun s=>f s+g s)=
      pairedFunctional beta r L f+pairedFunctional beta r L g := by
  have he : (∫s in (beta-r)..beta,Real.exp (L*(s-beta))*(f s+g s))=
      (∫s in (beta-r)..beta,Real.exp (L*(s-beta))*f s)+
        (∫s in (beta-r)..beta,Real.exp (L*(s-beta))*g s) := by
    rw [←intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun s:ℝ=>Real.exp (L*(s-beta))*f s)).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun s:ℝ=>Real.exp (L*(s-beta))*g s)).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  unfold pairedFunctional
  rw [he]
  ring

theorem pairedFunctional_smul (c:ℝ) (f:ℝ→ℝ) (beta r L:ℝ) :
    pairedFunctional beta r L (fun s=>c*f s)=c*pairedFunctional beta r L f := by
  have he : (∫s in (beta-r)..beta,Real.exp (L*(s-beta))*(c*f s))=
      c*(∫s in (beta-r)..beta,Real.exp (L*(s-beta))*f s) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  unfold pairedFunctional
  rw [he]
  ring

theorem pairedFunctional_const (c beta r L:ℝ) :
    pairedFunctional beta r L (fun _=>c)=c := by
  have hh := pairedFunctional_exponential c 0 beta r L
  simpa only [zero_mul,Real.exp_zero,mul_one,add_zero,pairedFactor] using hh

#print axioms pairedFunctional_add
#print axioms pairedFunctional_const
end SynergyAnalytic
