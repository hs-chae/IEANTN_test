import BoxPacketTransport
import BoxTrivialTransport
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Linearity and congruence for the actual transport operator. -/
namespace RHOcticPush.BoxPerron
open Real Set MeasureTheory
set_option maxHeartbeats 0

lemma transport_congr {a b : ℝ} (hab : a ≤ b) {F G : ℝ → ℂ}
    (h : EqOn F G (Icc a b)) : transport a b F = transport a b G := by
  unfold transport
  rw [h ⟨le_rfl,hab⟩,h ⟨hab,le_rfl⟩]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [h (by simpa [uIcc_of_le hab] using hx)]

lemma transport_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {F : ℝ → ℂ} (hF : ContinuousOn F (Icc a b)) :
    IntervalIntegrable (fun x => F x/(x:ℂ)^2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro x hx
  have hh := (hF x hx).div ((Complex.continuous_ofReal.continuousAt.pow 2).continuousWithinAt)
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ha.trans_le hx.1).ne'))
  simpa only [Pi.div_def, Pi.pow_def] using hh

lemma transport_add {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {F G : ℝ → ℂ}
    (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b)) :
    transport a b (fun x => F x+G x) = transport a b F+transport a b G := by
  unfold transport
  simp_rw [add_div]
  rw [intervalIntegral.integral_add (transport_integrable ha hab hF)
    (transport_integrable ha hab hG)]
  ring

lemma transport_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {F G : ℝ → ℂ}
    (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b)) :
    transport a b (fun x => F x-G x) = transport a b F-transport a b G := by
  unfold transport
  simp_rw [sub_div]
  rw [intervalIntegral.integral_sub (transport_integrable ha hab hF)
    (transport_integrable ha hab hG)]
  ring

lemma zeroSum_continuousOn {a b : ℝ} (h : SourceIntegratedPsi)
    (ha : 1 < a) (hab : a ≤ b) :
    ContinuousOn (fun x => ∑' r, zeroPrimitive x r) (Icc a b) :=
  continuousOn_tsum (zeroPrimitive_continuousOn ha)
    ((zeroCoefficient_summable h).norm.mul_left (exp (2*log b)))
    (fun r x hx => zeroPrimitive_uniform ha hab x hx r)

lemma trivialSum_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun x => (((∑' n : ℕ, trivialPrimitive n x) : ℝ) : ℂ)) (Icc a b) := by
  intro x hx
  exact (trivialTSum_hasDerivAt (ha.trans_le hx.1)).ofReal_comp.continuousAt.continuousWithinAt

#print axioms transport_add
#print axioms transport_sub
#print axioms zeroSum_continuousOn
end RHOcticPush.BoxPerron
