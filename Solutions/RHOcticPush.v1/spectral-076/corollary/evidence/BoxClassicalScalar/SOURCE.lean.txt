import SpectralComparison
import NormalizedFormula

/-! A conservative whole-ray scalar corollary of the full spectral Box pi
function. The existing scalar correction includes the entire prime-power and
Li2-offset allowances; no GM or Buthe mathematical source input is introduced. -/
namespace RHOcticPush.SpectralCorollary
open Real IEANTN RHLimit.PrimePower
set_option maxHeartbeats 0

/-- The full actual new function lies below the old pure function; this is a
comparison of explicit functions, not an application of the old GM theorem. -/
lemma whole_envelope_upper (f : ℝ → ℝ) {L : ℝ} (hL : 100 ≤ L) :
    Spectral076.piEnvelope f L <
      (f L+(14/5 : ℝ))*(Real.exp (L/2)/L) := by
  have h0 : 0 < L := by linarith
  have hnew := Spectral076.piEnvelope_strict_gain f (by linarith : (24:ℝ)≤L)
  have hold := RHOcticPush.Pi.strict_gain f (by linarith : (24:ℝ)≤L)
  have hc := RHLimit.PurePi.correction_upper hL
  have hn := RHLimit.PurePi.normalized_formula f (by linarith : (12:ℝ)≤L)
  have he : RHLimit.PurePi.envelope f L+2 =
      RHLimit.PurePi.normalized f L*(Real.exp (L/2)/L) := by
    unfold RHLimit.PurePi.normalized
    field_simp [h0.ne',Real.exp_ne_zero]
  have hh : RHLimit.PurePi.envelope f L+2 <
      (f L+(14/5 : ℝ))*(Real.exp (L/2)/L) := by
    rw [he,hn]
    exact mul_lt_mul_of_pos_right (by linarith) (div_pos (Real.exp_pos _) h0)
  linarith

/-- A quadratic comparison valid for all real L>=100. It retains the complete
proved Box moment expression, rather than substituting its leading term. -/
lemma box_quadratic_budget {L : ℝ} (hL : 100 ≤ L) :
    RHOcticPush.BoxTail.improvedBound L+(14/5 : ℝ) <
      L^2/(8*Real.pi)-(2/5)*L := by
  have h0 : 0 < L := by linarith
  have hlog : (23/5 : ℝ) ≤ Real.log L := by
    have ha : (23/5 : ℝ) ≤ Real.log 100 := by interval_decide 80 (trust := kernel)
    exact ha.trans (Real.log_le_log (by norm_num) hL)
  have hhalf : Real.log L ≤ L/2 := RHOcticPush.Applicability.log_le_half h0
  have ha : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb : Real.log 2 ≤ (7/10 : ℝ) := by linarith [Real.log_two_lt_d9]
  let t : ℝ := L/2-23/5
  let v : ℝ := L/2-Real.log L
  have hv0 : 0 ≤ v := by dsimp [v]; linarith
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have hvt : v ≤ t := by dsimp [v,t]; linarith
  have hs : v^2 ≤ t^2 := pow_le_pow_left₀ hv0 hvt 2
  have hm : 2*Real.log 2*v ≤ (7/5 : ℝ)*t := by
    exact mul_le_mul (by linarith : 2*Real.log 2 ≤ (7/5:ℝ)) hvt hv0 (by norm_num)
  have hbound : RHOcticPush.BoxTail.improvedBound L+(14/5 : ℝ) ≤
      (t^2+(7/5)*t+70871/50000+L)/(2*Real.pi)+(147/50 : ℝ) := by
    unfold RHOcticPush.BoxTail.improvedBound PsiSmoothing.envelope PsiSmoothing.v
    have hh := div_le_div_of_nonneg_right (by linarith :
      v^2+2*Real.log 2*v+2*(70871/100000)+L ≤
        t^2+(7/5)*t+70871/50000+L) (by positivity : 0 ≤ 2*Real.pi)
    dsimp [v] at hh
    linarith
  have hp : Real.pi ≤ (22/7 : ℝ) := by linarith [Real.pi_lt_d6]
  have hpL := mul_le_mul_of_nonneg_right hp h0.le
  have hmain : (t^2+(7/5)*t+70871/50000+L)/(2*Real.pi)+(147/50 : ℝ) <
      L^2/(8*Real.pi)-(2/5)*L := by
    apply (lt_sub_iff_add_lt).mpr
    apply (lt_div_iff₀ (by positivity : 0 < 8*Real.pi)).mpr
    have he : ((t^2+(7/5)*t+70871/50000+L)/(2*Real.pi)+(147/50 : ℝ)+(2/5)*L)*
        (8*Real.pi) =
        4*(t^2+(7/5)*t+70871/50000+L)+(588/25)*Real.pi+(16/5)*Real.pi*L := by
      field_simp [Real.pi_ne_zero]
      <;> ring
    rw [he]
    dsimp [t]
    nlinarith
  exact hbound.trans_lt hmain

/-- Complete all-real-logarithm function comparison. -/
theorem whole_box_stronger_classical {L : ℝ} (hL : 100 ≤ L) :
    Spectral076.piEnvelope RHOcticPush.BoxTail.improvedBound L <
      Real.exp (L/2)*(L/(8*Real.pi)-(2/5)) := by
  have h0 : 0 < L := by linarith
  calc
    _ < (RHOcticPush.BoxTail.improvedBound L+14/5)*(Real.exp (L/2)/L) :=
      whole_envelope_upper _ hL
    _ < (L^2/(8*Real.pi)-(2/5)*L)*(Real.exp (L/2)/L) :=
      mul_lt_mul_of_pos_right (box_quadratic_budget hL) (div_pos (Real.exp_pos _) h0)
    _ = _ := by field_simp [h0.ne',Real.pi_ne_zero] <;> ring

#print axioms whole_envelope_upper
#print axioms box_quadratic_budget
#print axioms whole_box_stronger_classical
end RHOcticPush.SpectralCorollary
