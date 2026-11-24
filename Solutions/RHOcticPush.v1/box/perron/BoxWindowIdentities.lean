import BoxTransportLinear

/-! All terms of the actual integrated explicit formula under exact Box transport. -/
namespace RHOcticPush.BoxPerron
open Real Set MeasureTheory IEANTN.RHSmoothing
set_option maxHeartbeats 0

lemma box_zero_summable (h : SourceIntegratedPsi) {L s : ℝ} (hL : 35 ≤ L)
    (hs : s = -1 ∨ s = 1) : Summable (zeroPacket box s L) := by
  obtain ⟨ha,hab⟩ := box_window_domain hL hs
  have he : zeroPacket box s L = fun r => (1/(2*delta L):ℂ)*
      transport (exp L*exp ((s-1)*delta L)) (exp L*exp ((s+1)*delta L))
        (fun x => zeroPrimitive x r) := by
    funext r
    exact (scaled_zero_transport (by linarith : 0 < L) s r).symm
  rw [he]
  exact (zero_transport_summable h ha hab).mul_left _

lemma scaled_zero_sum (h : SourceIntegratedPsi) {L s : ℝ} (hL : 35 ≤ L)
    (hs : s = -1 ∨ s = 1) :
    (1/(2*delta L):ℂ)*transport (exp L*exp ((s-1)*delta L))
      (exp L*exp ((s+1)*delta L)) (fun x => ∑' r,zeroPrimitive x r) =
        zeroAverage box s L := by
  obtain ⟨ha,hab⟩ := box_window_domain hL hs
  unfold zeroAverage
  rw [←zero_transport_tsum h ha hab, ←tsum_mul_left]
  apply tsum_congr
  intro r
  exact scaled_zero_transport (by linarith : 0 < L) s r

lemma scaled_main_transport {L : ℝ} (hL : 0 < L) (s : ℝ) :
    (1/(2*delta L):ℂ)*transport (exp L*exp ((s-1)*delta L))
      (exp L*exp ((s+1)*delta L)) (fun x : ℝ => (x:ℂ)^2/2) =
        (mainAverage box s L : ℂ) := by
  have hd := box_delta_pos hL
  have hF (x : ℝ) : HasDerivAt (fun y : ℝ => (y:ℂ)^2/2) (x:ℂ) x := by
    simpa only [id_eq, Pi.pow_def] using
      (((hasDerivAt_id x).ofReal_comp.pow 2).div_const 2).congr_deriv (by simp only [id_eq]; push_cast; ring)
  rw [scaled_transport_box (exp_pos L) hd s (fun x hx => hF x)
    (Complex.continuous_ofReal.intervalIntegrable _ _)]
  unfold mainAverage box window
  rw [←intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro u hu
  push_cast
  ring

lemma scaled_linear_transport {L : ℝ} (hL : 0 < L) (s : ℝ) (C : ℂ) :
    (1/(2*delta L):ℂ)*transport (exp L*exp ((s-1)*delta L))
      (exp L*exp ((s+1)*delta L)) (fun x : ℝ => (x:ℂ)*C) = C := by
  have hF (x : ℝ) : HasDerivAt (fun y : ℝ => (y:ℂ)*C) C x := by
    simpa only [id_eq, Complex.ofReal_one, one_mul] using
      (hasDerivAt_id x).ofReal_comp.mul_const C
  rw [scaled_transport_box (exp_pos L) (box_delta_pos hL) s
    (fun x hx => hF x) intervalIntegrable_const]
  norm_num
  ring

lemma constant_transport {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (C : ℂ) :
    transport a b (fun _ => C) = 0 := by
  rw [transport_of_hasDerivAt ha hab (fun x hx => hasDerivAt_const x C)
    intervalIntegrable_const]
  simp

lemma scaled_trivial_transport {L s : ℝ} (hL : 35 ≤ L) (hs : s = -1 ∨ s = 1) :
    (1/(2*delta L):ℂ)*transport (exp L*exp ((s-1)*delta L))
      (exp L*exp ((s+1)*delta L))
      (fun x => ((∑' n : ℕ,trivialPrimitive n x):ℝ)) = -(trivialAverage box s L : ℂ) := by
  obtain ⟨ha,hab⟩ := box_window_domain hL hs
  have hc : ContinuousOn (fun x => ((-trivial x:ℝ):ℂ))
      (uIcc (exp L*exp ((s-1)*delta L)) (exp L*exp ((s+1)*delta L))) := by
    rw [uIcc_of_le hab]
    exact Complex.continuous_ofReal.comp_continuousOn (trivial_continuousOn ha).neg
  rw [scaled_transport_box (exp_pos L) (box_delta_pos (by linarith : 0 < L)) s
    (fun x hx => (trivialTSum_hasDerivAt (ha.trans_le (by
      simpa only [min_eq_left hab] using hx.1))).ofReal_comp) hc.intervalIntegrable]
  unfold trivialAverage box window
  rw [←intervalIntegral.integral_ofReal, ←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro u hu
  push_cast
  ring

lemma scaled_psi1_transport {L s : ℝ} (hL : 35 ≤ L) (hs : s = -1 ∨ s = 1) :
    (1/(2*delta L):ℂ)*transport (exp L*exp ((s-1)*delta L))
      (exp L*exp ((s+1)*delta L)) (fun x => (psi1 x:ℂ)) = (average box s L:ℂ) := by
  obtain ⟨ha,hab⟩ := box_window_domain hL hs
  rw [psi1_transport ha hab]
  have he := congrArg Complex.ofReal (actual_box_log_integral hL s)
  push_cast at he
  have hr := intervalIntegral.integral_ofReal
    (f := fun x => Chebyshev.psi x/x) (μ := volume)
    (a := exp L*exp ((s-1)*delta L)) (b := exp L*exp ((s+1)*delta L))
  simp only [Complex.ofReal_div] at hr
  rw [hr]
  exact he.symm

#print axioms scaled_psi1_transport
#print axioms box_zero_summable
#print axioms scaled_zero_sum
#print axioms scaled_main_transport
#print axioms scaled_linear_transport
#print axioms constant_transport
#print axioms scaled_trivial_transport
end RHOcticPush.BoxPerron
