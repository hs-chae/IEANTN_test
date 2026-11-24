import SpectralWeightedTransport
import BoxExplicitFormula
import GMPair

/-! Actual compensation difference from the genuine general integrated source.
Complex phases and all endpoint terms are retained. No RH or desired numerical
bound is assumed. The only unformalized mathematical input is general Perron. -/
namespace RHOcticPush.Spectral076
open Real Complex Set MeasureTheory
open RHOcticPush.BoxPerron RHContinuation.Ramanujan
set_option maxHeartbeats 0

lemma gmPrimitive_eq_psi1 {x : ℝ} (hx : 0 ≤ x) :
    gmPrimitive x = psi1 x-x^2/2 := by
  rw [gmPrimitive_eq_integral hx,
    intervalIntegral.integral_sub (f := Chebyshev.psi) (g := fun t : ℝ => t)
      (Chebyshev.psi_mono.intervalIntegrable (μ := volume) (a := 0) (b := x))
      (continuous_id.intervalIntegrable 0 x), psi1_integral_from_zero]
  norm_num

lemma weighted_integrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    {F : ℝ → ℂ} (hF : ContinuousOn F (Icc a b)) :
    IntervalIntegrable (fun x => F x*(gmKernel x:ℂ)) volume a b := by
  have hK : ContinuousOn (fun x => (gmKernel x:ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn (gmKernel_continuousOn ha)
  exact (show ContinuousOn (fun x => F x*(gmKernel x:ℂ)) (uIcc a b) from
    by simpa only [uIcc_of_le hab,Pi.mul_def] using hF.mul hK).intervalIntegrable

lemma weighted_congr {a b : ℝ} (hab : a ≤ b) {F G : ℝ → ℂ}
    (h : EqOn F G (Icc a b)) : weightedTransport a b F=weightedTransport a b G := by
  unfold weightedTransport
  rw [h ⟨hab,le_rfl⟩,h ⟨le_rfl,hab⟩]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [h (by simpa only [uIcc_of_le hab] using hx)]

lemma weighted_add {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) {F G : ℝ → ℂ}
    (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b)) :
    weightedTransport a b (fun x => F x+G x)=weightedTransport a b F+weightedTransport a b G := by
  unfold weightedTransport
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add (weighted_integrable ha hab hF)
    (weighted_integrable ha hab hG)]
  ring

lemma weighted_sub {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) {F G : ℝ → ℂ}
    (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b)) :
    weightedTransport a b (fun x => F x-G x)=weightedTransport a b F-weightedTransport a b G := by
  unfold weightedTransport
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (weighted_integrable ha hab hF)
    (weighted_integrable ha hab hG)]
  ring

lemma weighted_neg (a b : ℝ) (F : ℝ → ℂ) :
    weightedTransport a b (fun x => -F x) = -weightedTransport a b F := by
  unfold weightedTransport
  simp only [neg_mul,intervalIntegral.integral_neg]
  ring

lemma weighted_constant {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (C : ℂ) :
    weightedTransport a b (fun _ => C) = 0 := by
  rw [weightedTransport_of_hasDerivAt ha hab (fun x hx => hasDerivAt_const x C)
    intervalIntegrable_const]
  simp

lemma weighted_linear {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (C : ℂ) :
    weightedTransport a b (fun x : ℝ => (x:ℂ)*C) =
      C*(∫ t in a..b,(gmWeight t:ℂ)) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => (y:ℂ)*C) C x := by
    simpa only [id_eq,Complex.ofReal_one,one_mul] using
      (hasDerivAt_id x).ofReal_comp.mul_const C
  rw [weightedTransport_of_hasDerivAt ha hab (fun x hx => hd x) intervalIntegrable_const,
    intervalIntegral.integral_const_mul]

lemma weighted_trivial {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    weightedTransport a b (fun x => ((∑' n : ℕ,trivialPrimitive n x):ℝ)) =
      -(∫ t in a..b,(IEANTN.RHSmoothing.trivial t:ℂ)*(gmWeight t:ℂ)) := by
  have hc : ContinuousOn (fun x => ((-IEANTN.RHSmoothing.trivial x:ℝ):ℂ)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact Complex.continuous_ofReal.comp_continuousOn (trivial_continuousOn ha).neg
  rw [weightedTransport_of_hasDerivAt ha hab
    (fun x hx => (trivialTSum_hasDerivAt (ha.trans_le (by
      simpa only [min_eq_left hab] using hx.1))).ofReal_comp) hc.intervalIntegrable]
  simp only [Complex.ofReal_neg,neg_mul,intervalIntegral.integral_neg]

lemma actual_compensation_weighted {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ((RHOcticPush.GM.error b-RHOcticPush.GM.error a:ℝ):ℂ) =
      weightedTransport a b (fun x => (gmPrimitive x:ℂ)) := by
  have hcomp := actual_riemann_compensation ha hab
  have hparts := actual_gm_integral_parts ha hab
  have he : RHOcticPush.GM.error b-RHOcticPush.GM.error a =
      gmPrimitive b*gmWeight b-gmPrimitive a*gmWeight a+
        ∫ t in a..b,gmPrimitive t*gmKernel t := by
    unfold RHOcticPush.GM.error
    rw [hcomp]
    simpa only [gmWeight,div_eq_mul_inv,one_mul,intervalIntegral.integral_of_le hab]
      using hparts
  have hh := congrArg Complex.ofReal he
  unfold weightedTransport
  push_cast at hh
  rw [←intervalIntegral.integral_ofReal] at hh
  simpa only [Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_add] using hh

/-- The actual signed compensation identity required by the0.076 program.
No numerical coefficient or target bound appears among its assumptions. -/
theorem actual_source_transport (h : SourceIntegratedPsi) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) :
    ((RHOcticPush.GM.error b-RHOcticPush.GM.error a:ℝ):ℂ) =
      -weightedTransport a b (fun x => ∑' r,zeroPrimitive x r) -
      (Real.log (2*Real.pi):ℂ)*(∫ t in a..b,(gmWeight t:ℂ)) +
      ∫ t in a..b,(IEANTN.RHSmoothing.trivial t:ℂ)*(gmWeight t:ℂ) := by
  obtain ⟨C,hC⟩ := h
  have hs : SourceIntegratedPsi := ⟨C,hC⟩
  have hz := zeroSum_continuousOn hs ha hab
  have hl : ContinuousOn (fun x : ℝ => (x:ℂ)*(Real.log (2*Real.pi):ℂ)) (Icc a b) := by
    fun_prop
  have hc : ContinuousOn (fun _x : ℝ => C) (Icc a b) := continuousOn_const
  have ht := trivialSum_continuousOn (b := b) ha
  have he : EqOn (fun x => (gmPrimitive x:ℂ))
      (fun x => -(∑' r,zeroPrimitive x r)-(x:ℂ)*(Real.log (2*Real.pi):ℂ)+C-
        ((∑' n : ℕ,trivialPrimitive n x):ℝ)) (Icc a b) := by
    intro x hx
    dsimp only
    rw [gmPrimitive_eq_psi1 (by linarith [hx.1]:0≤x)]
    simp only [Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_ofNat]
    rw [(hC x (ha.trans_le hx.1)).2]
    ring
  rw [actual_compensation_weighted ha hab,weighted_congr hab he]
  have h1 := weighted_sub ha hab ((hz.neg.sub hl).add hc) ht
  have h2 := weighted_add ha hab (hz.neg.sub hl) hc
  have h3 := weighted_sub ha hab hz.neg hl
  simp only [Pi.neg_def,Pi.sub_def,Pi.add_def] at h1 h2 h3
  rw [h1,h2,h3,weighted_neg,weighted_constant ha hab C,weighted_linear ha hab,
    weighted_trivial ha hab]
  ring

#print axioms gmPrimitive_eq_psi1
#print axioms actual_compensation_weighted
#print axioms actual_source_transport
end RHOcticPush.Spectral076
