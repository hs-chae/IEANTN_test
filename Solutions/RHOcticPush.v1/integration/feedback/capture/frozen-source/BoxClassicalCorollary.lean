import BoxClassicalScalar
import SpectralNetwork

/-! A clean stronger same-onset corollary of the actual four-source spectral
Box bound. This is weaker than that complete function; the clean subtractive
constant improves the old1/3 corollary. Source packages remain explicit. -/
namespace RHOcticPush.SpectralCorollary
open Real IEANTN RHOcticPush.BoxPerron
set_option maxHeartbeats 0

/-- Every real logarithm above100, with all actual Box providers constructed. -/
theorem actual_box_pi_log (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    {L : ℝ} (hL : 100 ≤ L) :
    |primeCounting (Real.exp L)-IEANTN.Li (Real.exp L)| <
      Real.exp (L/2)*(L/(8*Real.pi)-(2/5)) := by
  exact (Spectral076.actual_box_pi rh hN hI hB (by linarith : (35:ℝ)≤L)).trans_lt
    (whole_box_stronger_classical hL)

/-- The target concerns ordinary prime counting and the offset Li2 observable,
not Riemann's weighted J or the unoffset principal-value logarithmic integral. -/
theorem actual_box_pi_ray (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    {x : ℝ} (hx : Real.exp 100 ≤ x) :
    |primeCounting x-IEANTN.Li x| <
      Real.sqrt x*(Real.log x/(8*Real.pi)-(2/5)) := by
  have hx0 : 0 < x := (Real.exp_pos 100).trans_le hx
  have hL : 100 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 100) hx
  have h := actual_box_pi_log rh hN hI hB hL
  simpa only [Real.exp_half,Real.exp_log hx0] using h

/-- The same mathematical conclusion with the exact four canonical node inputs;
no former GM or Buthe transfer premise is introduced by the scalar comparison. -/
theorem actual_box_pi_ray_canonical (rh : RH.v1.hypothesis)
    (hi : IntegratedPerron.v1.formula) (hn : Nicolas.v1.spectral_bound)
    (hb : BPTOffOrdinate.v1.bound) {x : ℝ} (hx : Real.exp 100 ≤ x) :
    |primeCounting x-IEANTN.Li x| <
      Real.sqrt x*(Real.log x/(8*Real.pi)-(2/5)) := by
  exact actual_box_pi_ray rh hn (RHOcticPush.SpectralCanonical.canonical_source hi) hb hx

/-- Exact entire-function gain in the clean right-hand sides, at the same onset.
The new and old analytic source packages are different, not a same-premise claim. -/
theorem clean_subtractive_gain (x : ℝ) :
    Real.sqrt x*(Real.log x/(8*Real.pi)-(1/3))-
      Real.sqrt x*(Real.log x/(8*Real.pi)-(2/5)) = Real.sqrt x/15 := by ring

theorem clean_subtractive_strict {x : ℝ} (hx : Real.exp 100 ≤ x) :
    Real.sqrt x*(Real.log x/(8*Real.pi)-(2/5)) <
      Real.sqrt x*(Real.log x/(8*Real.pi)-(1/3)) := by
  have hx0 : 0 < x := (Real.exp_pos 100).trans_le hx
  have h := clean_subtractive_gain x
  have hp : 0 < Real.sqrt x/15 := by positivity
  linarith

/-- Certified illustrative coefficients at the common onset. These finite
kernel inequalities are not assumptions of the whole-ray result above. -/
theorem clean_coefficient_at100 :
    (357887/100000 : ℝ) < 100/(8*Real.pi)-(2/5) ∧
    100/(8*Real.pi)-(2/5) < (357888/100000 : ℝ) := by
  constructor
  · apply lt_sub_iff_add_lt.mpr
    apply (lt_div_iff₀ (by positivity : 0 < 8*Real.pi)).mpr
    nlinarith [Real.pi_lt_d6]
  · apply sub_lt_iff_lt_add.mpr
    apply (div_lt_iff₀ (by positivity : 0 < 8*Real.pi)).mpr
    nlinarith [Real.pi_gt_d6]

theorem old_clean_coefficient_at100 :
    (364554/100000 : ℝ) < 100/(8*Real.pi)-(1/3) ∧
    100/(8*Real.pi)-(1/3) < (364555/100000 : ℝ) := by
  constructor
  · apply lt_sub_iff_add_lt.mpr
    apply (lt_div_iff₀ (by positivity : 0 < 8*Real.pi)).mpr
    nlinarith [Real.pi_lt_d20]
  · apply sub_lt_iff_lt_add.mpr
    apply (div_lt_iff₀ (by positivity : 0 < 8*Real.pi)).mpr
    nlinarith [Real.pi_gt_d6]

lemma normalized_point100 :
    (RHOcticPush.BoxTail.improvedBound 100+RHLimit.PurePi.correction 100)/100 <
      (35704/10000 : ℝ) := by
  unfold RHLimit.PurePi.correction RHOcticPush.BoxTail.improvedBound
    PsiSmoothing.envelope PsiSmoothing.v
  interval_decide 100 (trust := kernel) <;>
    simp [LeanCert.Core.MathConst.toReal,div_eq_mul_inv,mul_inv_rev]

/-- The complete function has a smaller point value than the clean2/5 bound. -/
theorem full_function_at100 :
    Spectral076.piEnvelope RHOcticPush.BoxTail.improvedBound 100 <
      (35704/10000 : ℝ)*Real.exp 50 := by
  have hnew := Spectral076.piEnvelope_strict_gain RHOcticPush.BoxTail.improvedBound
    (by norm_num : (24:ℝ)≤100)
  have hold := RHOcticPush.Pi.strict_gain RHOcticPush.BoxTail.improvedBound
    (by norm_num : (24:ℝ)≤100)
  have hn := RHLimit.PurePi.normalized_formula RHOcticPush.BoxTail.improvedBound
    (by norm_num : (12:ℝ)≤100)
  have he : RHLimit.PurePi.envelope RHOcticPush.BoxTail.improvedBound 100+2 =
      ((RHOcticPush.BoxTail.improvedBound 100+RHLimit.PurePi.correction 100)/100)*
        Real.exp 50 := by
    rw [←hn]
    unfold RHLimit.PurePi.normalized
    norm_num
    field_simp [Real.exp_ne_zero]
  exact (show Spectral076.piEnvelope RHOcticPush.BoxTail.improvedBound 100 <
    RHLimit.PurePi.envelope RHOcticPush.BoxTail.improvedBound 100+2 by linarith).trans
      (by rw [he]; exact mul_lt_mul_of_pos_right normalized_point100 (Real.exp_pos 50))

#print axioms actual_box_pi_log
#print axioms actual_box_pi_ray
#print axioms actual_box_pi_ray_canonical
#print axioms clean_subtractive_gain
#print axioms clean_subtractive_strict
#print axioms clean_coefficient_at100
#print axioms old_clean_coefficient_at100
#print axioms full_function_at100
end RHOcticPush.SpectralCorollary
