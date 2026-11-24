import FeedbackPi
import BoxClassicalCorollary

/-! Convenient clean21/50 corollary of the stronger complete feedback function.
The full original35-ray and all raw J/Q information remain in FeedbackPi. -/
namespace RHOcticPush.PrimeSquareFeedback
open Real IEANTN RHOcticPush.BoxPerron
set_option maxHeartbeats 0

lemma simplified_envelope_upper {L : ℝ} (hL : 100 ≤ L) :
    simplifiedEnvelope RHOcticPush.BoxTail.improvedBound L <
      (RHOcticPush.BoxTail.improvedBound L+(113/100 : ℝ))*(Real.exp (L/2)/L) := by
  have h0 : 0 < L := by linarith
  have hold := RHOcticPush.SpectralCorollary.whole_envelope_upper
    RHOcticPush.BoxTail.improvedBound hL
  have hc := mul_lt_mul_of_pos_right coefficient_lower
    (div_pos (Real.exp_pos (L/2)) h0)
  have hg := simplified_envelope_gain RHOcticPush.BoxTail.improvedBound L
  have hh : simplifiedEnvelope RHOcticPush.BoxTail.improvedBound L <
      Spectral076.piEnvelope RHOcticPush.BoxTail.improvedBound L-
        (167/100 : ℝ)*(Real.exp (L/2)/L) := by
    have he : (2*Real.log 4-(11/10 : ℝ))*Real.exp (L/2)/L =
        (2*Real.log 4-(11/10 : ℝ))*(Real.exp (L/2)/L) := by ring
    rw [he] at hg
    linarith
  calc
    _ < _ := hh
    _ < (RHOcticPush.BoxTail.improvedBound L+14/5)*(Real.exp (L/2)/L)-
        (167/100 : ℝ)*(Real.exp (L/2)/L) := sub_lt_sub_right hold _
    _ = _ := by ring

lemma box_feedback_budget {L : ℝ} (hL : 100 ≤ L) :
    RHOcticPush.BoxTail.improvedBound L+(113/100 : ℝ) <
      L^2/(8*Real.pi)-(21/50)*L := by
  have h0 : 0 < L := by linarith
  have hlog : (23/5 : ℝ) ≤ Real.log L := by
    have ha : (23/5 : ℝ) ≤ Real.log 100 := by interval_decide 80 (trust := kernel)
    exact ha.trans (Real.log_le_log (by norm_num) hL)
  have hhalf := RHOcticPush.Applicability.log_le_half h0
  have hb : Real.log 2 ≤ (7/10 : ℝ) := by linarith [Real.log_two_lt_d9]
  let t : ℝ := L/2-23/5
  let v : ℝ := L/2-Real.log L
  have hv0 : 0 ≤ v := by dsimp [v]; linarith
  have hvt : v ≤ t := by dsimp [v,t]; linarith
  have hs : v^2 ≤ t^2 := pow_le_pow_left₀ hv0 hvt 2
  have hm : 2*Real.log 2*v ≤ (7/5 : ℝ)*t :=
    mul_le_mul (by linarith : 2*Real.log 2≤(7/5:ℝ)) hvt hv0 (by norm_num)
  have hbound : RHOcticPush.BoxTail.improvedBound L+(113/100 : ℝ) ≤
      (t^2+(7/5)*t+70871/50000+L)/(2*Real.pi)+(127/100 : ℝ) := by
    unfold RHOcticPush.BoxTail.improvedBound PsiSmoothing.envelope PsiSmoothing.v
    have hh := div_le_div_of_nonneg_right (by linarith :
      v^2+2*Real.log 2*v+2*(70871/100000)+L ≤
        t^2+(7/5)*t+70871/50000+L) (by positivity : 0≤2*Real.pi)
    dsimp [v] at hh
    linarith
  have hp : Real.pi ≤ (22/7 : ℝ) := by linarith [Real.pi_lt_d6]
  have hpL := mul_le_mul_of_nonneg_right hp h0.le
  have hmain : (t^2+(7/5)*t+70871/50000+L)/(2*Real.pi)+(127/100 : ℝ) <
      L^2/(8*Real.pi)-(21/50)*L := by
    apply lt_sub_iff_add_lt.mpr
    apply (lt_div_iff₀ (by positivity : 0<8*Real.pi)).mpr
    have he : ((t^2+(7/5)*t+70871/50000+L)/(2*Real.pi)+(127/100 : ℝ)+(21/50)*L)*
        (8*Real.pi) =
        4*(t^2+(7/5)*t+70871/50000+L)+(254/25)*Real.pi+(84/25)*Real.pi*L := by
      field_simp [Real.pi_ne_zero]
      <;> ring
    rw [he]
    dsimp [t]
    nlinarith
  exact hbound.trans_lt hmain

theorem envelope_clean {L : ℝ} (hL : 100 ≤ L) :
    envelope RHOcticPush.BoxTail.improvedBound L <
      Real.exp (L/2)*(L/(8*Real.pi)-(21/50)) := by
  have h0 : 0 < L := by linarith
  calc
    _ < simplifiedEnvelope RHOcticPush.BoxTail.improvedBound L := envelope_lt_simplified hL _
    _ < (RHOcticPush.BoxTail.improvedBound L+113/100)*(Real.exp (L/2)/L) :=
      simplified_envelope_upper hL
    _ < (L^2/(8*Real.pi)-(21/50)*L)*(Real.exp (L/2)/L) :=
      mul_lt_mul_of_pos_right (box_feedback_budget hL) (div_pos (Real.exp_pos _) h0)
    _ = _ := by field_simp [h0.ne',Real.pi_ne_zero] <;> ring

theorem actual_box_pi_clean (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    {x : ℝ} (hx : Real.exp 100 ≤ x) :
    |primeCounting x-IEANTN.Li x| < Real.sqrt x*(Real.log x/(8*Real.pi)-(21/50)) := by
  have hx0 : 0<x := (Real.exp_pos 100).trans_le hx
  have hL : 100 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 100) hx
  have h := (actual_box_pi_log rh hN hI hB (by linarith : (35:ℝ)≤Real.log x)).trans_lt
    (envelope_clean hL)
  simpa only [Real.exp_half,Real.exp_log hx0] using h

theorem actual_box_pi_canonical (rh : RH.v1.hypothesis)
    (hi : IntegratedPerron.v1.formula) (hn : Nicolas.v1.spectral_bound)
    (hb : BPTOffOrdinate.v1.bound) {x : ℝ} (hx : Real.exp 35 ≤ x) :
    |primeCounting x-IEANTN.Li x| ≤ envelope RHOcticPush.BoxTail.improvedBound (Real.log x) :=
  actual_box_pi rh hn (RHOcticPush.SpectralCanonical.canonical_source hi) hb hx

theorem actual_box_pi_clean_canonical (rh : RH.v1.hypothesis)
    (hi : IntegratedPerron.v1.formula) (hn : Nicolas.v1.spectral_bound)
    (hb : BPTOffOrdinate.v1.bound) {x : ℝ} (hx : Real.exp 100 ≤ x) :
    |primeCounting x-IEANTN.Li x| < Real.sqrt x*(Real.log x/(8*Real.pi)-(21/50)) :=
  actual_box_pi_clean rh hn (RHOcticPush.SpectralCanonical.canonical_source hi) hb hx

theorem clean_gain (x : ℝ) :
    Real.sqrt x*(Real.log x/(8*Real.pi)-(2/5))-
      Real.sqrt x*(Real.log x/(8*Real.pi)-(21/50)) = Real.sqrt x/50 := by ring

theorem full_function_at100 : envelope RHOcticPush.BoxTail.improvedBound 100 <
    (35537/10000 : ℝ)*Real.exp 50 := by
  have hold := RHOcticPush.SpectralCorollary.full_function_at100
  have hg := envelope_strict_gain (by norm_num : (100:ℝ)≤100)
    RHOcticPush.BoxTail.improvedBound
  norm_num at hg
  linarith

#print axioms simplified_envelope_upper
#print axioms box_feedback_budget
#print axioms envelope_clean
#print axioms actual_box_pi_clean
#print axioms actual_box_pi_canonical
#print axioms actual_box_pi_clean_canonical
#print axioms clean_gain
#print axioms full_function_at100
end RHOcticPush.PrimeSquareFeedback
