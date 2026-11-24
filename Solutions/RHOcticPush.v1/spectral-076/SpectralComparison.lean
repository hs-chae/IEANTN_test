import SpectralPi

/-! Comparison of complete old/new mathematical functions, on their common ray.
The actual source inputs for the two valid providers differ; this scalar theorem
does not hide them or assert a best-known-in-the-literature result. -/
namespace RHOcticPush.Spectral076
open Real Set
set_option maxHeartbeats 0

lemma leading_lower {b L : ℝ} (hb : 0 ≤ b) (hL : b < L) :
    (693/5000 : ℝ)*(Real.exp (L/2)/L^2) ≤ RHOcticPush.GM.leading b (Real.exp L) := by
  have h0 : 0 < L := lt_of_le_of_lt hb hL
  have hd : 0 < L*(L-b) := mul_pos h0 (sub_pos.mpr hL)
  have hd' : L*(L-b) ≤ L^2 := by nlinarith
  have hn : 0 ≤ (693/5000 : ℝ)*Real.exp (L/2) := by positivity
  have h := div_le_div_of_nonneg_left hn hd hd'
  unfold RHOcticPush.GM.leading
  rw [Real.log_exp,←Real.exp_half]
  convert! h using 1 <;> ring

lemma evolved_lower {L : ℝ} (hL : 24 ≤ L) :
    (14 : ℝ)+(76/1000)*(Real.exp (L/2)/L^2) ≤
      RHOcticPush.GM.evolvedBound (Real.exp L) := by
  have h5 := leading_lower (b := 5) (by norm_num) (by linarith : (5:ℝ)<L)
  have h6 := leading_lower (b := 6) (by norm_num) (by linarith : (6:ℝ)<L)
  have hE : 0 ≤ Real.exp (L/2)/L^2 := by positivity
  have he : RHLimit.Spectral.refinedBound (Real.exp L) =
      (361/25 : ℝ)+RHOcticPush.GM.leading 6 (Real.exp L) := by
    rfl
  unfold RHOcticPush.GM.evolvedBound
  rw [if_pos (Real.exp_le_exp.mpr (by linarith : (15:ℝ)≤L))]
  apply le_min
  · rw [he]
    nlinarith
  · nlinarith

lemma piEnvelope_difference (f : ℝ → ℝ) (L : ℝ) :
    RHOcticPush.Pi.envelope f L-piEnvelope f L =
      RHOcticPush.GM.evolvedBound (Real.exp L)-profile L := by
  unfold RHOcticPush.Pi.envelope piEnvelope
  ring

/-- A strict improvement in the entire explicit ordinary-pi envelope, including
the unchanged prime-power and Li-offset terms, for every common logarithm. -/
theorem piEnvelope_strict_gain (f : ℝ → ℝ) {L : ℝ} (hL : 24 ≤ L) :
    (14 : ℝ) < RHOcticPush.Pi.envelope f L-piEnvelope f L := by
  rw [piEnvelope_difference]
  have hn := profile_lt_076 hL
  have ho := evolved_lower hL
  linarith

#print axioms evolved_lower
#print axioms piEnvelope_strict_gain
end RHOcticPush.Spectral076
