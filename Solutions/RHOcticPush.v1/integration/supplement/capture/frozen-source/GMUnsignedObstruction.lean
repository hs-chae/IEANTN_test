import GMPair
/-! A limitation of the existing unsigned GM majorant, not an impossibility
claim about the arithmetic oscillatory error or the open0.076 theorem. -/
namespace RHOcticPush.GM
open Real Set MeasureTheory IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0
lemma envelope_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ gmEnvelope t := by
  unfold gmEnvelope
  positivity
lemma kernel_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ gmKernel t := by
  have hl : 0 < log t := log_pos ht
  unfold gmKernel
  positivity
lemma unsigned_integrand_lower {t x : ℝ} (ht : 1 < t) (htx : t ≤ x) :
    (231/5000 : ℝ)/(sqrt t*(log x)^2) ≤ gmEnvelope t*gmKernel t := by
  have ht0 : 0 < t := by linarith
  have hx : 1 < x := ht.trans_le htx
  have hl : 0 < log t := log_pos ht
  have hL : log t ≤ log x := log_le_log ht0 htx
  have hD : 0 < sqrt t*(log t)^2 := by positivity
  have hDD : sqrt t*(log t)^2 ≤ sqrt t*(log x)^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le hL 2) (sqrt_nonneg t)
  have hE : (231/5000 : ℝ)*t*sqrt t ≤ gmEnvelope t := by
    unfold gmEnvelope
    have : 0 ≤ (919/500 : ℝ)*t+19851/10000+(5097/10000 : ℝ)/t := by positivity
    linarith
  have hK : 1/(t^2*(log t)^2) ≤ gmKernel t := by
    unfold gmKernel
    have : 0 ≤ 2/(t^2*(log t)^3) := by positivity
    linarith
  calc
    _ ≤ (231/5000 : ℝ)/(sqrt t*(log t)^2) :=
      div_le_div_of_nonneg_left (by norm_num) hD hDD
    _ = ((231/5000 : ℝ)*t*sqrt t)*(1/(t^2*(log t)^2)) := by
      have hs := sq_sqrt ht0.le
      field_simp [ht0.ne', hl.ne', (sqrt_pos.mpr ht0).ne']
      nlinarith
    _ ≤ _ := mul_le_mul hE hK (by positivity) (envelope_nonneg ht0)

lemma reciprocal_sqrt_integral {x : ℝ} (hx : 0 < x) :
    (∫ t in x/4..x, 1/sqrt t) = sqrt x := by
  have hab : x/4 ≤ x := by linarith
  have hc : ContinuousOn (fun t : ℝ => 1/sqrt t) (Icc (x/4) x) := by
    intro t ht
    exact (continuousAt_const.div (Real.continuous_sqrt.continuousAt)
      (sqrt_ne_zero'.mpr (by linarith [ht.1] : 0 < t))).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := x/4) (b := x) (fun t ht => by
      have ht0 : 0 < t := by
        have := (uIcc_of_le hab ▸ ht).1
        linarith
      apply ((hasDerivAt_sqrt ht0.ne').const_mul 2).congr_deriv
      field_simp [(sqrt_pos.mpr ht0).ne']
      <;> ring) (hc.intervalIntegrable_of_Icc hab)
  rw [h, Real.sqrt_div hx.le]
  norm_num
  ring


lemma unsigned_boundary_lower {x : ℝ} (hx : 1 < x) :
    (231/5000 : ℝ)*sqrt x/(log x)^2 ≤ gmEnvelope x*gmWeight x := by
  have hx0 : 0 < x := by linarith
  have hE : (231/5000 : ℝ)*x*sqrt x ≤ gmEnvelope x := by
    unfold gmEnvelope
    have : 0 ≤ (919/500 : ℝ)*x+19851/10000+(5097/10000 : ℝ)/x := by positivity
    linarith
  have hw : 0 ≤ gmWeight x := by unfold gmWeight; positivity
  have h := mul_le_mul_of_nonneg_right hE hw
  have he : ((231/5000 : ℝ)*x*sqrt x)*gmWeight x =
      (231/5000 : ℝ)*sqrt x/(log x)^2 := by
    unfold gmWeight
    field_simp [hx0.ne']
  simpa only [he] using h

/-- Even a short upper-end interval forces the unsigned GM allowance above0.076.
This concerns the positive majorant gmTransport, not the actual oscillatory error. -/
theorem unsigned_transport_lower {a x : ℝ} (ha : 3 ≤ a) (hx : 4*a ≤ x) :
    (231/2500 : ℝ)*sqrt x/(log x)^2 ≤ gmTransport a x := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have ha1 : 1 < a := by linarith
  have hxa : a ≤ x/4 := by linarith
  have hxx : x/4 ≤ x := by linarith
  have h4 : 1 < x/4 := by linarith
  let g : ℝ → ℝ := fun t => gmEnvelope t*gmKernel t
  have hg : IntegrableOn g (Ioc a x) :=
    ((gmEnvelope_continuousOn (by linarith : 0 < a)).mul
      (gmKernel_continuousOn ha1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hg0 : 0 ≤ᵐ[volume.restrict (Ioc a x)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (envelope_nonneg (by linarith [ht.1]))
      (kernel_nonneg (by linarith [ht.1]))
  have hs : Ioc (x/4) x ⊆ Ioc a x := fun t ht => ⟨lt_of_le_of_lt hxa ht.1,ht.2⟩
  have hmono := setIntegral_mono_set hg hg0 (Filter.Eventually.of_forall fun t ht => hs ht)
  have hlowc : ContinuousOn (fun t : ℝ => (231/5000)/(sqrt t*(log x)^2))
      (Icc (x/4) x) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact (continuousAt_const.div
      (Real.continuous_sqrt.continuousAt.mul continuousAt_const)
      (mul_ne_zero (sqrt_pos.mpr ht0).ne' (pow_ne_zero 2 (log_pos hx1).ne'))).continuousWithinAt
  have hlowi : IntervalIntegrable
      (fun t : ℝ => (231/5000)/(sqrt t*(log x)^2)) volume (x/4) x :=
    hlowc.intervalIntegrable_of_Icc hxx
  have hlowOn := (intervalIntegrable_iff_integrableOn_Ioc_of_le hxx).mp hlowi
  have hcomp : (∫ t in Ioc (x/4) x, (231/5000 : ℝ)/(sqrt t*(log x)^2)) ≤
      ∫ t in Ioc (x/4) x, g t := by
    apply integral_mono_ae hlowOn (hg.mono_set hs)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact unsigned_integrand_lower (by linarith [ht.1]) ht.2
  have heval : (∫ t in Ioc (x/4) x, (231/5000 : ℝ)/(sqrt t*(log x)^2)) =
      (231/5000 : ℝ)*sqrt x/(log x)^2 := by
    have he : (fun t : ℝ => (231/5000 : ℝ)/(sqrt t*(log x)^2)) =
        fun t => (1/sqrt t)*((231/5000 : ℝ)/(log x)^2) := by funext t; ring
    rw [he, ← intervalIntegral.integral_of_le hxx, intervalIntegral.integral_mul_const,
      reciprocal_sqrt_integral hx0]
    ring
  rw [heval] at hcomp
  have hanchor : 0 ≤ gmEnvelope a*gmWeight a := by
    apply mul_nonneg (envelope_nonneg (by linarith))
    unfold gmWeight
    positivity
  have hboundary := unsigned_boundary_lower hx1
  unfold gmTransport
  dsimp only [g] at hmono hcomp
  have he : (231/2500 : ℝ)*sqrt x/(log x)^2 =
      2*((231/5000 : ℝ)*sqrt x/(log x)^2) := by ring
  rw [he]
  linarith only [hmono,hcomp,hanchor,hboundary]

/-- The unmodified unsigned transport cannot itself be a0.076 allowance. -/
theorem unsigned_exceeds_076 {a x : ℝ} (ha : 3 ≤ a) (hx : 4*a ≤ x) :
    (19/250 : ℝ)*sqrt x/(log x)^2 < gmTransport a x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  calc
    _ < (231/2500 : ℝ)*sqrt x/(log x)^2 := by
      apply div_lt_div_of_pos_right _ (sq_pos_of_pos (log_pos hx1))
      exact mul_lt_mul_of_pos_right (by norm_num) (sqrt_pos.mpr hx0)
    _ ≤ _ := unsigned_transport_lower ha hx
#print axioms unsigned_exceeds_076
#print axioms unsigned_transport_lower
#print axioms unsigned_integrand_lower
#print axioms reciprocal_sqrt_integral
end RHOcticPush.GM
