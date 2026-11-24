import BoxIntegratedPopulation

/-! Exact scaled transport on a logarithmic box. All normalization factors and
both physical endpoints are explicit, including the actual factor2delta. -/
namespace RHOcticPush.BoxPerron
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def window (x s d u : ℝ) : ℝ := x*Real.exp ((s+u)*d)

lemma window_pos {x : ℝ} (hx : 0 < x) (s d u : ℝ) : 0 < window x s d u := by
  unfold window
  positivity

lemma window_endpoints {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (s : ℝ) :
    x*Real.exp ((s-1)*d) ≤ x*Real.exp ((s+1)*d) := by
  apply mul_le_mul_of_nonneg_left _ hx.le
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Transport of ANY C1 primitive equals the actual logarithmic box average of
its derivative. This is a mathematical operator identity, not a Box EF premise. -/
theorem scaled_transport_box {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (s : ℝ)
    {F F' : ℝ → ℂ}
    (hF : ∀ v ∈ uIcc (x*Real.exp ((s-1)*d)) (x*Real.exp ((s+1)*d)),
      HasDerivAt F (F' v) v)
    (hi : IntervalIntegrable F' volume (x*Real.exp ((s-1)*d))
      (x*Real.exp ((s+1)*d))) :
    (1/(2*d) : ℂ)*transport (x*Real.exp ((s-1)*d)) (x*Real.exp ((s+1)*d)) F =
      ∫ u in (-1:ℝ)..1, (1/2:ℂ)*F' (window x s d u) := by
  have ht := transport_of_hasDerivAt (by positivity : 0 < x*Real.exp ((s-1)*d))
    (window_endpoints hx hd s) hF hi
  have hc := complex_box_logchange x s d hx hd (fun v => F' v/(v:ℂ))
  have he : (∫ v in x*Real.exp ((s-1)*d)..x*Real.exp ((s+1)*d), F' v/(v:ℂ)) =
      (d:ℂ)*(∫ u in (-1:ℝ)..1, F' (window x s d u)) := by
    rw [←hc, ←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    have hw : (window x s d u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (window_pos hx s d u).ne'
    change F' (window x s d u)/(window x s d u:ℂ)*(d:ℂ)*(window x s d u:ℂ) = _
    field_simp
  rw [ht, he, intervalIntegral.integral_const_mul]
  have hd0 : (d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  field_simp

#print axioms scaled_transport_box
end RHOcticPush.BoxPerron
