import PurePiConsumers
namespace RHLimit.PurePi
open Real IEANTN RHLimit.PrimePower
set_option maxHeartbeats 0

noncomputable def correction (L : ℝ) : ℝ :=
  2*log 4+(693/5000:ℝ)/(L-6)+L/(2*exp (L/4))+
    L*log (L/log 2)/exp (L/6)+(411/25:ℝ)*L/exp (L/2)

lemma normalized_formula (f : ℝ → ℝ) {L : ℝ} (hL : 12 ≤ L) :
    normalized f L = f L+correction L := by
  have hL0 : L ≠ 0 := by linarith
  have hd : L-6 ≠ 0 := by linarith
  have h4 : exp (L/2) = exp (L/4)*exp (L/4) := by
    rw [← exp_add]; congr 1; ring
  have h6 : exp (L/2) = exp (L/3)*exp (L/6) := by
    rw [← exp_add]; congr 1; ring
  have hr4 : exp (L/4)/exp (L/2) = 1/exp (L/4) := by
    rw [h4]; field_simp
  have hr6 : exp (L/3)/exp (L/2) = 1/exp (L/6) := by
    rw [h6]; field_simp
  calc
    normalized f L = f L+2*log 4+(693/5000:ℝ)/(L-6)+
        L/2*(exp (L/4)/exp (L/2))+
        L*log (L/log 2)*(exp (L/3)/exp (L/2))+
        (411/25:ℝ)*L/exp (L/2) := by
      unfold normalized envelope elementaryRemainder
      field_simp [hL0, hd, exp_ne_zero]
      <;> ring
    _ = f L+correction L := by rw [hr4, hr6]; unfold correction; ring

lemma exponential_quadratic {L : ℝ} (hL : 100 ≤ L) :
    100*L^2 ≤ exp (L/6) := by
  let t : ℝ := (L-100)/6
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have he : 1+t+t^2/2 ≤ exp t := by
    have h := sum_le_exp_of_nonneg ht 3
    simp [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have ha : (1000000:ℝ) ≤ exp (100/6:ℝ) := by
    interval_decide 80 (trust := kernel)
  have hm := mul_le_mul ha he (by positivity : 0 ≤ 1+t+t^2/2) (exp_pos _).le
  have hx : L = 100+6*t := by dsimp [t]; ring
  have hh : exp (100/6:ℝ)*exp t = exp (L/6) := by
    rw [← exp_add]; congr 1; dsimp [t]; ring
  rw [hh] at hm
  have hpoly : 100*L^2 ≤ 1000000*(1+t+t^2/2) := by
    rw [hx]
    nlinarith [sq_nonneg t]
  exact hpoly.trans hm

lemma correction_upper {L : ℝ} (hL : 100 ≤ L) : correction L < 14/5 := by
  have hL0 : 0 < L := by linarith
  have hs := exponential_quadratic hL
  have hs4 : 100*L^2 ≤ exp (L/4) := hs.trans (exp_le_exp.mpr (by linarith))
  have hs2 : 100*L^2 ≤ exp (L/2) := hs.trans (exp_le_exp.mpr (by linarith))
  have hlog : log (L/log 2) ≤ L := by
    rw [log_div hL0.ne' (log_pos (by norm_num : (1:ℝ)<2)).ne']
    have h1 := log_le_sub_one_of_pos hL0
    have h2 : (-1:ℝ) ≤ log (log 2) := by interval_decide 80 (trust := kernel)
    linarith
  have h0 : 2*log 4 < (139/50:ℝ) := by interval_decide 80 (trust := kernel)
  have h1 : (693/5000:ℝ)/(L-6) ≤ 1/500 := by
    apply (div_le_iff₀ (by linarith : 0<L-6)).mpr
    linarith
  have h2 : L/(2*exp (L/4)) ≤ 1/1000 := by
    apply (div_le_iff₀ (by positivity : 0<2*exp (L/4))).mpr
    nlinarith
  have h3 : L*log (L/log 2)/exp (L/6) ≤ 1/100 := by
    apply (div_le_iff₀ (exp_pos _)).mpr
    have hh := mul_le_mul_of_nonneg_left hlog hL0.le
    nlinarith
  have h4 : (411/25:ℝ)*L/exp (L/2) ≤ 1/500 := by
    apply (div_le_iff₀ (exp_pos _)).mpr
    nlinarith
  unfold correction
  linarith

/-- Whole-ray comparison, not just sampled numerical evidence. -/
theorem ch_normalized_improves_classical {L : ℝ} (hL : 100 ≤ L) :
    normalized RHSmoothing.chBound L < L^2/(8*π)-L/3 := by
  have hc := correction_upper hL
  have hL0 : 0 < L := by linarith
  have hlog4 : (23/5:ℝ) ≤ log L := by
    have h : (23/5:ℝ) ≤ log 100 := by interval_decide 80 (trust := kernel)
    exact h.trans (log_le_log (by norm_num) hL)
  have hloghalf : log L ≤ L/2 := by
    have h := log_le_sub_one_of_pos (div_pos hL0 (by norm_num : (0:ℝ)<2))
    rw [log_div hL0.ne' (by norm_num)] at h
    linarith [log_two_lt_d9]
  have hcl : 0 < log (10/π) := log_pos ((one_lt_div pi_pos).mpr (by linarith [pi_lt_four]))
  have hcu : log (10/π) ≤ (29/25:ℝ) := by
    interval_decide 80 (trust := kernel) <;> simp [LeanCert.Core.MathConst.toReal, div_eq_mul_inv]
  let u : ℝ := L/2-log L+log (10/π)
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu : u ≤ L/2-86/25 := by dsimp [u]; linarith
  have hut : 0 ≤ L/2-86/25 := by linarith
  have hu2 : u^2 ≤ (L/2-86/25)^2 := pow_le_pow_left₀ hu0 hu 2
  have hbound : RHSmoothing.chBound L ≤
      (158/1000:ℝ)*L+(L/2-86/25)^2/(2*π)+181/1000 := by
    unfold RHSmoothing.chBound
    change (158/1000:ℝ)*L+(u^2-u/3)/(2*π)+181/1000 ≤ _
    have hd := div_le_div_of_nonneg_right (show u^2-u/3 ≤ (L/2-86/25)^2 by nlinarith)
      (by positivity : 0 ≤ 2*π)
    linarith
  have hp : π ≤ 22/7 := by linarith [pi_lt_d6]
  have he : (L^2/4-(L/2-86/25)^2)/(2*π) ≥
      (7/44:ℝ)*((86/25:ℝ)*L-(86/25:ℝ)^2) := by
    have hn : 0 ≤ (86/25:ℝ)*L-(86/25:ℝ)^2 := by nlinarith
    apply (le_div_iff₀ (by positivity : 0<2*π)).mpr
    have hm := mul_le_mul_of_nonneg_left hp hn
    nlinarith
  rw [normalized_formula _ (by linarith)]
  have hmain : (158/1000:ℝ)*L+(L/2-86/25)^2/(2*π)+181/1000+14/5 <
      L^2/(8*π)-L/3 := by
    have heq : L^2/(8*π)-(L/2-86/25)^2/(2*π) =
        (L^2/4-(L/2-86/25)^2)/(2*π) := by ring
    linarith
  linarith

#print axioms normalized_formula
#print axioms exponential_quadratic
#print axioms correction_upper
#print axioms ch_normalized_improves_classical
end RHLimit.PurePi
