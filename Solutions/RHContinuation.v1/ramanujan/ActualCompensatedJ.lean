import ActualLiAbelModel
import FiniteMangoldtAbel
namespace RHContinuation.Ramanujan
open Real Set MeasureTheory

/-- Exact endpoint-subtracted finite-J identity. It uses the actual principal
value li and actual Mangoldt/psi, with no analytic identity hypothesis.
Identifying finite J with IEANTN.riemannPrimeCounting is a separate obligation. -/
theorem actual_finite_J_compensation {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (FiniteMangoldtAbel.J b-IEANTN.li b-(Chebyshev.psi b-b)/log b)-
      (FiniteMangoldtAbel.J a-IEANTN.li a-(Chebyshev.psi a-a)/log a) =
        ∫ t in Set.Ioc a b, (Chebyshev.psi t-t)/(t*(log t)^2) := by
  have hJ := FiniteMangoldtAbel.abel ha hab
  have hLi := actual_li_abel_model ha hab
  have hc : IntegrableOn (fun t : ℝ => 1/(log t)^2) (Set.Ioc a b) := by
    apply (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    intro t ht
    have ht1 : 1 < t := ha.trans_le ht.1
    exact (continuousAt_const.div ((continuousAt_log (by linarith : t ≠ 0)).pow 2)
      (pow_ne_zero 2 (log_pos ht1).ne')).continuousWithinAt
  have he : (∫ t in Set.Ioc a b, (Chebyshev.psi t-t)/(t*(log t)^2)) =
      (∫ t in Set.Ioc a b, Chebyshev.psi t/(t*(log t)^2))-
        ∫ t in Set.Ioc a b, 1/(log t)^2 := by
    rw [← integral_sub (FiniteMangoldtAbel.psi_log_kernel_integrable ha) hc]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : log t ≠ 0 := (log_pos (ha.trans ht.1)).ne'
    field_simp [ht0,hl0]
    <;> ring
  rw [he,hLi]
  simp only [sub_div] at *
  linarith

#print axioms actual_finite_J_compensation
end RHContinuation.Ramanujan
