/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.AnalyticGlue

/-! Recover the reported quantitative height40 onset using the stronger direct
Büthe input on the short early interval. This does not assume Ramanujan positivity. -/
namespace RamanujanPV.EarlyMiddle
open Real IEANTN RamanujanPV.Middle RamanujanPV.LiBarriers RamanujanPV.FiniteMiddle
set_option maxHeartbeats 0

noncomputable def delta : ℝ := 1 / 50000000
noncomputable def uniformError : ℝ := delta + 100000000 * 43 * rho ^ 39

lemma early_pi_error {L : ℝ} (h39 : 39 ≤ L) (h43 : L ≤ 43)
    (hbuthe : ButheDeficit19) (hbelow : ButheBelow19) : |piErrorLog L| ≤ delta := by
  have hL : 0 < L := by linarith
  have hx2 : (2 : ℝ) ≤ exp L := by linarith [add_one_le_exp L]
  have hxU : exp L ≤ (10000000000000000000 : ℝ) :=
    (exp_le_exp.mpr h43).trans RamanujanPV.exp43_le_1e19
  have hP := hbelow (exp L) hx2 hxU
  have hD := hbuthe (exp L) hx2 hxU
  have habs : |primeCounting (exp L) - IEANTN.li (exp L)| =
      IEANTN.li (exp L) - primeCounting (exp L) := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hP)]
  have hscaled := mul_le_mul_of_nonneg_left
    (show IEANTN.li (exp L) - primeCounting (exp L) ≤
      sqrt (exp L) / log (exp L) * ((39 / 20 : ℝ) + (39 / 10 : ℝ) / log (exp L) +
        (39 / 2 : ℝ) / log (exp L) ^ 2) by linarith)
    (show 0 ≤ L * exp (-L) by positivity)
  rw [log_exp, ← exp_half] at hscaled
  have hid : L * exp (-L) * (exp (L / 2) / L *
      ((39 / 20 : ℝ) + (39 / 10 : ℝ) / L + (39 / 2 : ℝ) / L ^ 2)) =
      ((39 / 20 : ℝ) + (39 / 10 : ℝ) / L + (39 / 2 : ℝ) / L ^ 2) * exp (-L / 2) := by
    have hE : exp (-L) * exp (L / 2) = exp (-L / 2) := by
      rw [← exp_add]; congr 1; ring
    field_simp [hL.ne']
    nlinarith [hE]
  rw [hid] at hscaled
  have hcoef : (39 / 20 : ℝ) + (39 / 10 : ℝ) / L + (39 / 2 : ℝ) / L ^ 2 ≤ 11 / 5 := by
    apply (le_div_iff₀ (show (0 : ℝ) < L^2 by positivity)).mp ?_ -- use direct denominator clearing below
    field_simp [hL.ne']
    nlinarith [sq_nonneg (L-39)]
  have he : exp (-L / 2) ≤ rho ^ 19 :=
    (exp_le_exp.mpr (by linarith : -L / 2 ≤ -(19 : ℝ))).trans (exp_neg_nat_upper 19)
  have hbound : ((39 / 20 : ℝ) + (39 / 10 : ℝ) / L + (39 / 2 : ℝ) / L ^ 2) * exp (-L / 2) ≤ delta := by
    calc
      _ ≤ (11 / 5 : ℝ) * rho ^ 19 := mul_le_mul hcoef he (exp_pos _).le (by norm_num)
      _ ≤ _ := by unfold delta rho; norm_num
  unfold piErrorLog
  rw [abs_mul, abs_of_pos (show 0 < L * exp (-L) by positivity), habs]
  exact hscaled.trans hbound

lemma normalized_bounds {L : ℝ} (h39 : 39 ≤ L) (h43 : L ≤ 43)
    (herror : |piErrorLog L| ≤ delta)
    (hoffset : LiOffsetIdentity) (hli2 : 0 ≤ IEANTN.li 2 ∧ IEANTN.li 2 ≤ 2)
    (hlog2 : (2 / 3 : ℝ) ≤ log 2) :
    S10 L - uniformError ≤ W L ∧ W L ≤ U10 L + uniformError := by
  have hL0 : 0 < L := by linarith
  have hx : (2 : ℝ) ≤ exp L := by linarith [add_one_le_exp L]
  have hscale : 0 ≤ L * exp (-L) := by positivity
  have hl := mul_le_mul_of_nonneg_left (actual_li_lower hx hoffset hli2.1 hlog2) hscale
  rw [mul_sub, scaled_F10 hL0] at hl
  have hu := mul_le_mul_of_nonneg_left
    (actual_li_upper (exp_le_exp.mpr (by linarith : (17 : ℝ) ≤ L)) hoffset hli2.2 hlog2) hscale
  have huId : L * exp (-L) *
      (F10 (exp L) + 3 * (Nat.factorial 10 : ℝ) * exp L / log (exp L) ^ 11 + 100000000) =
      U10 L + 100000000 * L * exp (-L) := by
    rw [mul_add, mul_add, scaled_F10 hL0]
    unfold U10
    rw [log_exp, exp_neg]
    norm_num
    field_simp [hL0.ne', (exp_pos L).ne']
    <;> ring
  rw [huId] at hu
  have hconst : 100000000 * L * exp (-L) ≤ 100000000 * 43 * rho ^ 39 := by
    have he : exp (-L) ≤ rho ^ 39 :=
      (exp_le_exp.mpr (by linarith : -L ≤ -(39 : ℝ))).trans (exp_neg_nat_upper 39)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h43 (by norm_num)) he (exp_pos _).le (by norm_num)
  have hw : W L = piErrorLog L + L * exp (-L) * IEANTN.li (exp L) := by
    unfold W piErrorLog; ring
  obtain ⟨heL, heU⟩ := abs_le.mp herror
  unfold uniformError
  constructor <;> rw [hw] <;> nlinarith

lemma early_numeric_margin :
    (37 / 200 : ℝ) < positivePoly 43 - negativePoly 40 -
      43 ^ 4 * (43 / 39 * uniformError + uniformError * (2 * U10 40 + uniformError)) := by
  unfold positivePoly negativePoly uniformError delta rho U10 S10
  norm_num

/-- Direct literature estimates plus already proved integral barriers give the
entire missing early real interval; no external Ramanujan statement is used. -/
theorem normalized_early_gap {L : ℝ} (h40 : 40 ≤ L) (h43 : L ≤ 43)
    (hbuthe : ButheDeficit19) (hbelow : ButheBelow19)
    (hoffset : LiOffsetIdentity) (hli2 : 0 ≤ IEANTN.li 2 ∧ IEANTN.li 2 ≤ 2)
    (hlog2 : (2 / 3 : ℝ) ≤ log 2) : (37 / 200 : ℝ) < normalizedGap L := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 < L := by linarith
  have hU := (normalized_bounds (by linarith : 39 ≤ L) h43
    (early_pi_error (by linarith) h43 hbuthe hbelow) hoffset hli2 hlog2).2
  have hD := (normalized_bounds (by linarith : 39 ≤ L-1) (by linarith : L-1 ≤ 43)
    (early_pi_error (by linarith) (by linarith) hbuthe hbelow) hoffset hli2 hlog2).1
  have hg := normalized_gap_lower hL1 hU hD
  have hp := positivePoly_antitone hL0 h43
  have hn := negativePoly_antitone (by norm_num : (0 : ℝ) < 40) h40
  have hUpper := U10_antitone (by norm_num : (0 : ℝ) < 40) h40
  have hfac : L / (L - 1) ≤ (43 : ℝ) / 39 := by
    apply div_le_div₀ (by norm_num) h43 (by norm_num)
    linarith
  have hpow : L ^ 4 ≤ (43 : ℝ) ^ 4 := pow_le_pow_left₀ hL0.le h43 4
  have hE : 0 ≤ uniformError := by unfold uniformError delta rho; positivity
  have hU0 := U10_nonneg hL0
  have hLoss : L ^ 4 * (L / (L - 1) * uniformError +
      uniformError * (2 * U10 L + uniformError)) ≤
      (43 : ℝ) ^ 4 * (43 / 39 * uniformError + uniformError * (2 * U10 40 + uniformError)) := by
    gcongr
  linarith [early_numeric_margin]

 theorem actual_early_gap {x : ℝ} (hx40 : exp 40 ≤ x) (hx43 : x ≤ exp 43)
    (hbuthe : ButheDeficit19) (hbelow : ButheBelow19)
    (hoffset : LiOffsetIdentity) (hli2 : 0 ≤ IEANTN.li 2 ∧ IEANTN.li 2 ≤ 2)
    (hlog2 : (2 / 3 : ℝ) ≤ log 2) :
    (37 / 200 : ℝ) * x ^ 2 / log x ^ 6 < RamanujanPV.gap x := by
  have hx0 : 0 < x := (exp_pos 40).trans_le hx40
  have hL : (40 : ℝ) ≤ log x := by simpa using log_le_log (exp_pos 40) hx40
  have hLU : log x ≤ (43 : ℝ) := by simpa using log_le_log hx0 hx43
  have hg := gap_of_normalized_gap (by linarith : 0 < log x)
    (normalized_early_gap hL hLU hbuthe hbelow hoffset hli2 hlog2)
  simpa only [exp_log hx0] using hg

#print axioms early_pi_error
#print axioms normalized_early_gap
#print axioms actual_early_gap
end RamanujanPV.EarlyMiddle
