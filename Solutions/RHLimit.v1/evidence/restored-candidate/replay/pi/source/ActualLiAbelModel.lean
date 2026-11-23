import LiPVDefinition
namespace RHContinuation.Ramanujan
open Real Set MeasureTheory

lemma actual_li_abel_primitive_derivative {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => IEANTN.li t-t/log t) (1/(log t)^2) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : log t ≠ 0 := (log_pos ht).ne'
  have h := (actual_li_hasDerivAt ht).sub
    ((hasDerivAt_id t).div (hasDerivAt_log ht0) hl0)
  convert! h using 1 <;> simp only [id_eq] <;> field_simp <;> ring

/-- Exact model term needed to subtract li from a finite Mangoldt Abel sum.
This uses the actual principal-value li, with no series/gamma/derivative input. -/
theorem actual_li_abel_model {y x : ℝ} (hy : 1 < y) (hyx : y ≤ x) :
    (∫ t in Set.Ioc y x, 1/(log t)^2) =
      (IEANTN.li x-x/log x)-(IEANTN.li y-y/log y) := by
  have hd : ∀ t ∈ uIcc y x,
      HasDerivAt (fun t : ℝ => IEANTN.li t-t/log t) (1/(log t)^2) t := by
    intro t ht
    rw [uIcc_of_le hyx] at ht
    exact actual_li_abel_primitive_derivative (hy.trans_le ht.1)
  have hc : ContinuousOn (fun t : ℝ => 1/(log t)^2) (uIcc y x) := by
    apply continuousOn_const.div
    · apply ContinuousOn.pow
      apply Real.continuousOn_log.mono
      intro t ht
      rw [uIcc_of_le hyx] at ht
      exact ne_of_gt (by linarith [ht.1])
    · intro t ht
      rw [uIcc_of_le hyx] at ht
      exact pow_ne_zero 2 (log_pos (hy.trans_le ht.1)).ne'
  rw [← intervalIntegral.integral_of_le hyx]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

#print axioms actual_li_abel_model
end RHContinuation.Ramanujan
