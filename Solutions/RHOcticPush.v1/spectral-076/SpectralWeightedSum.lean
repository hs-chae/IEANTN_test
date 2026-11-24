import SpectralWeightedTransport
import BoxZeroTransport
import BetaDecimal

/-! Full actual-zero interchange for the signed logarithmic transport. -/
namespace RHOcticPush.Spectral076
open Real Complex Set MeasureTheory
open RHOcticPush.BoxPerron RHContinuation.Ramanujan
set_option maxHeartbeats 0

lemma gmKernel_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ gmKernel x := by
  unfold gmKernel
  have hl := Real.log_pos hx
  positivity

lemma gmKernel_le {a x : ℝ} (ha : 1 < a) (hax : a ≤ x) : gmKernel x ≤ gmKernel a := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := ha0.trans_le hax
  have hl : 0 < Real.log a := Real.log_pos ha
  have hlog := Real.log_le_log ha0 hax
  have h2 := mul_le_mul (pow_le_pow_left₀ ha0.le hax 2)
    (pow_le_pow_left₀ hl.le hlog 2) (by positivity) (by positivity)
  have h3 := mul_le_mul (pow_le_pow_left₀ ha0.le hax 2)
    (pow_le_pow_left₀ hl.le hlog 3) (by positivity) (by positivity)
  unfold gmKernel
  exact add_le_add
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) h2)
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) h3)

lemma weightedIntegrand_continuous {a b : ℝ} (ha : 1 < a)
    (r : IEANTN.RHSmoothing.Zero) :
    ContinuousOn (fun t => zeroPrimitive t r*(gmKernel t : ℂ)) (Icc a b) :=
  (zeroPrimitive_continuousOn ha r).mul
    (Complex.continuous_ofReal.comp_continuousOn (gmKernel_continuousOn ha))

lemma weightedIntegrand_uniform {a b t : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (ht : t ∈ Icc a b) (r : IEANTN.RHSmoothing.Zero) :
    ‖zeroPrimitive t r*(gmKernel t : ℂ)‖ ≤
      (Real.exp (2*Real.log b)*gmKernel a)*‖zeroCoefficient r‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (gmKernel_nonneg (ha.trans_le ht.1))]
  have hp := zeroPrimitive_uniform ha hab t ht r
  have hk := gmKernel_le ha ht.1
  calc
    _ ≤ (Real.exp (2*Real.log b)*‖zeroCoefficient r‖)*gmKernel a :=
      mul_le_mul hp hk (gmKernel_nonneg (ha.trans_le ht.1)) (by positivity)
    _ = _ := by ring

lemma weighted_zero_integral_summable {a b : ℝ} (h : SourceIntegratedPsi)
    (ha : 1 < a) (hab : a ≤ b) :
    Summable (fun r => ∫ t in a..b,zeroPrimitive t r*(gmKernel t : ℂ)) := by
  apply ((((zeroCoefficient_summable h).norm.mul_left
    (Real.exp (2*Real.log b)*gmKernel a))).mul_right |b-a|).of_norm_bounded
  intro r
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  exact weightedIntegrand_uniform ha hab
    (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using ht)) r

theorem weighted_zero_summable {a b : ℝ} (h : SourceIntegratedPsi)
    (ha : 1 < a) (hab : a ≤ b) :
    Summable (fun r => weightedTransport a b (fun t => zeroPrimitive t r)) := by
  exact (((zeroPrimitive_summable h ha hab (show b ∈ Icc a b from ⟨hab,le_rfl⟩)).mul_right
    (gmWeight b : ℂ)).sub
    ((zeroPrimitive_summable h ha hab (show a ∈ Icc a b from ⟨le_rfl,hab⟩)).mul_right
      (gmWeight a : ℂ))).add (weighted_zero_integral_summable h ha hab)

/-- Complete infinite-family interchange; both endpoint evaluations retained. -/
theorem weighted_zero_tsum {a b : ℝ} (h : SourceIntegratedPsi)
    (ha : 1 < a) (hab : a ≤ b) :
    (∑' r,weightedTransport a b (fun t => zeroPrimitive t r)) =
      weightedTransport a b (fun t => ∑' r,zeroPrimitive t r) := by
  have hi := interval_tsum_uniform hab zeroCoefficient (zeroCoefficient_summable h)
    (fun r t => zeroPrimitive t r*(gmKernel t : ℂ))
    (weightedIntegrand_continuous ha)
    (fun r t ht => weightedIntegrand_uniform ha hab ht r)
  have hA := (zeroPrimitive_summable h ha hab
    (show a ∈ Icc a b from ⟨le_rfl,hab⟩)).mul_right (gmWeight a : ℂ)
  have hB := (zeroPrimitive_summable h ha hab
    (show b ∈ Icc a b from ⟨hab,le_rfl⟩)).mul_right (gmWeight b : ℂ)
  unfold weightedTransport
  rw [(hB.sub hA).tsum_add (weighted_zero_integral_summable h ha hab),hB.tsum_sub hA,hi]
  simp only [tsum_mul_right]

#print axioms weighted_zero_tsum
#print axioms weighted_zero_summable
end RHOcticPush.Spectral076
