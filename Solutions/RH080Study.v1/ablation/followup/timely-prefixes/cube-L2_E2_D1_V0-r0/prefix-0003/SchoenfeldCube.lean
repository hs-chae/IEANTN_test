import ThetaCube

namespace FreshCubes
open Real Finset
open MertensPositive
noncomputable section
set_option maxHeartbeats 0

theorem schoenfeld_profile (hS : SourceSchoenfeld61) (rh : RiemannHypothesis)
    {n : ℝ} (hn : 45/4 ≤ n) (ha : 2300000000 ≤ n^3) :
    n^2/log n - ((n+1)*sqrt (n+1)*(3*log (n+1)-2)/(4*π)) <
      count (n^3) ((n+1)^3) := by
  have hn0 : 0 < n := by linarith
  have hU0 : 0 < 3*log (n+1) := mul_pos (by norm_num) (log_pos (by linarith))
  have hLn := (log_room hn).1
  have hlog := log_le_log hn0 (by linarith : n ≤ n+1)
  have hmain := main_room hn
  have hroom := (log_room hn).2
  have hab : n^3 ≤ (n+1)^3 := pow_le_pow_left₀ hn0.le (by linarith) 3
  let E (m : ℝ) := m * sqrt m * (3*log m - 2) * (3*log m) / (8*π)
  have hmono : E n ≤ E (n+1) := by
    have ht' : 0 ≤ 3*log (n+1)-2 := by linarith
    have ha' : 0 ≤ (n+1)*sqrt (n+1)*(3*log (n+1)-2) := by positivity
    dsimp [E]
    gcongr <;> linarith
  have hA : Chebyshev.theta (n^3) - n^3 < E n := by
    have h := (abs_lt.mp (hS rh _ ha)).2
    rw [sqrt_cube hn0.le, log_pow] at h
    simpa [E] using h
  have hB : -E (n+1) < Chebyshev.theta ((n+1)^3) - (n+1)^3 := by
    have h := (abs_lt.mp (hS rh _ (ha.trans hab))).1
    rw [sqrt_cube (by positivity : 0 ≤ n+1), log_pow] at h
    simpa [E] using h
  have hbridge := cube_bridge (show 2 ≤ n by linarith)
  have hcancel : 2 * E (n+1) =
      ((n+1)*sqrt (n+1)*(3*log (n+1)-2)/(4*π)) * (3*log (n+1)) := by
    unfold E
    ring
  apply lt_of_sub_pos
  apply pos_of_mul_pos_left _ hU0.le
  rw [sub_mul, sub_mul, hcancel.symm, mul_comm (n^2/log n)]
  nlinarith only [hA,hB,hmono,hbridge,hmain,hroom,hn0]

def switch : ℝ := 2154433

lemma switch_buthe {n : ℝ} (h : n ≤ switch) (hn : 0 ≤ n) :
    (n+1)^3 ≤ (10:ℝ)^19 := by
  refine (pow_le_pow_left₀ (show 0 ≤ n+1 by positivity) (show n+1 ≤ switch+1 by linarith) 3).trans ?_
  norm_num [switch]

lemma switch_log : (14583/1000 : ℝ) ≤ log switch := by
  have hratio : (10:ℝ)^19 ≤ (100000/99999) * switch^3 := by norm_num [switch]
  have h := log_le_log (by positivity : 0 < (10:ℝ)^19) hratio
  rw [log_mul (by norm_num : (100000/99999:ℝ) ≠ 0)
    (by norm_num [switch] : switch^3 ≠ 0), log_pow, log_pow, log_ten_eq] at h
  have hh := log_le_sub_one_of_pos (by norm_num : 0 < (100000/99999:ℝ))
  norm_num at h
  linarith [log_two_gt_d9, log_five_gt_d9]

lemma hExp72915 : (146775/100:ℝ) ≤ exp ((14583/1000)/2) := by
  have h := sum_le_exp_of_nonneg (show (0:ℝ) ≤ (14583/1000)/2 by norm_num) 22
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
  linarith

/-- Polynomial-over-square-root envelope, valid on a continuous ray. -/
lemma poly_over_root {m : ℝ} (hm : 0 < m) (ht : (14583/1000:ℝ) ≤ log m) :
    log m * (3*log m-2) / (4*π*sqrt m) ≤
      ((14583/1000)*(3*(14583/1000)-2))/(4*(314159/100000)*(146775/100)) := by
  let u : ℝ := 14583/1000
  let v := log m-u
  have hv : 0 ≤ v := sub_nonneg.mpr ht
  have hp : log m * (3*log m-2) ≤
       (u*(3*u-2))*(1+v/2+v^2/8) := by
    have h : log m = u+v := by dsimp [v]; ring
    rw [h]
    dsimp [u]
    nlinarith only [hv, sq_nonneg v]
  have he : 1+v/2+v^2/8 ≤ exp (v/2) := by
    have h := sum_le_exp_of_nonneg (show 0 ≤ v/2 by positivity) 3
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h
    linarith only [h]
  have heq : exp (u/2) * exp (v/2) = sqrt m := by
    rw [← exp_add, show u/2+v/2 = log m/2 by dsimp [v]; ring,
      ← log_sqrt hm.le, exp_log (sqrt_pos.mpr hm)]
  have hl : (146775/100:ℝ) * exp (v/2) ≤ sqrt m := by
    rw [← heq]
    exact mul_le_mul_of_nonneg_right hExp72915 (exp_nonneg _)
  have hpoly : 0 ≤ u*(3*u-2) := by norm_num [u]
  have hpc := mul_le_mul_of_nonneg_left he hpoly
  have hconst : (0:ℝ) < (4*(314159/100000)*(146775/100)) := by norm_num
  apply (div_le_div_iff₀ (by positivity) hconst).mpr
  change (log m * (3*log m-2)) * (4*(314159/100000)*(146775/100)) ≤
    (u*(3*u-2)) * (4*π*sqrt m)
  have hpi : (314159/100000:ℝ) ≤ π := by linarith [pi_gt_d20]
  calc
    _ ≤ (u*(3*u-2)) * exp (v/2) * (4*(314159/100000)*(146775/100)) :=
      mul_le_mul_of_nonneg_right (hp.trans hpc) hconst.le
    _ = (u*(3*u-2)) * (4*(314159/100000)*((146775/100)*exp (v/2))) := by ring
    _ ≤ _ := by gcongr

theorem schoenfeld_96699 (hS : SourceSchoenfeld61) (rh : RiemannHypothesis)
    {n : ℝ} (hn : switch ≤ n) :
    (96699/100000:ℝ) * (n^2/log n) < count (n^3) ((n+1)^3) := by
  have hn0 : 0 < n := (by norm_num [switch] : 0 < switch).trans_le hn
  have hnq : (45/4:ℝ) ≤ n := (by norm_num [switch] : 45/4 ≤ switch).trans hn
  have hL0 : 0 < log n := by linarith [(log_room hnq).1]
  have hla : 2300000000 ≤ n^3 := (by norm_num [switch] : (2300000000:ℝ) ≤ switch^3).trans
    (pow_le_pow_left₀ (by norm_num [switch]) hn 3)
  have hU : log n ≤ log (n+1) := log_le_log hn0 (by linarith)
  have ht : (14583/1000:ℝ) ≤ log (n+1) :=
    switch_log.trans (log_le_log (by norm_num [switch]) hn |>.trans hU)
  have hbound := poly_over_root (show 0 < n+1 by positivity) ht
  have hM : (n+1)^2 ≤ (1000001/1000000)*n^2 := by
    have hn' : (2100000:ℝ) ≤ n := (by norm_num [switch] : (2100000:ℝ) ≤ switch).trans hn
    nlinarith only [hn', mul_nonneg (sub_nonneg.mpr hn') hn0.le]
  let w : ℝ := ((14583/1000)*(3*(14583/1000)-2))/(4*(314159/100000)*(146775/100))
  have hw : 0 ≤ w := by norm_num [w]
  have hW : (1000001/1000000:ℝ)*w ≤ (3301/100000) := by norm_num [w]
  have ht0 : 0 ≤ 3*log (n+1)-2 := by linarith
  have hmul : ((n+1)*sqrt (n+1)*(3*log (n+1)-2)/(4*π)) * log n ≤
      (3301/100000)*n^2 := by
    calc
      _ ≤ ((n+1)*sqrt (n+1)*(3*log (n+1)-2)/(4*π)) * log (n+1) := by
        exact mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ ((n+1)*sqrt (n+1)*(3*log (n+1)-2)/(4*π)))
      _ = (n+1)^2 * (log (n+1)*(3*log (n+1)-2)/(4*π*sqrt (n+1))) := by
        field_simp [pi_pos.ne', (sqrt_pos.mpr (show 0 < n+1 by positivity)).ne']
        ring_nf
        rw [sq_sqrt (show 0 ≤ 1+n by positivity)]
        ring
      _ ≤ (n+1)^2 * w := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
      _ ≤ ((1000001/1000000)*n^2) * w := mul_le_mul_of_nonneg_right hM hw
      _ ≤ _ := by linear_combination (n^2)*hW
  have hd := (le_div_iff₀ hL0).mpr hmul
  have hp := schoenfeld_profile hS rh hnq hla
  have hsplit : (96699/100000:ℝ) * (n^2/log n) =
      n^2/log n - ((3301/100000)*n^2)/log n := by ring
  rw [hsplit]
  linarith

theorem cube_from_theta (hS : SourceSchoenfeld61) (rh : RiemannHypothesis)
    (hlo : PublishedButheThetaLower) (hhi : PublishedButheThetaUpper)
    {c n : ℝ} (hn : 45/4 ≤ n) (hc : c ≤ 96699/100000)
    (hc' : (19/30) ≤ (1-c)*sqrt n) :
    c * (n^2/log n) < count (n^3) ((n+1)^3) := by
  have hn0 : 0 < n := by linarith
  have hL0 : 0 < log n := by linarith [(log_room hn).1]
  by_cases h : switch ≤ n
  · exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans_lt (schoenfeld_96699 hS rh h)
  · have hf := buthe_profile hlo hhi hn (switch_buthe (le_of_not_ge h) hn0.le)
    apply lt_of_le_of_lt _ hf
    have hmul := mul_le_mul_of_nonneg_right hc' (show 0 ≤ n*sqrt n/log n by positivity)
    have ht : (1-c)*sqrt n*(n*sqrt n/log n) = (1-c)*(n^2/log n) := by
      calc
        _ = (1-c)*(n*(sqrt n)^2/log n) := by ring
        _ = _ := by rw [sq_sqrt hn0.le]; ring
    rw [ht] at hmul
    have he : (19/30:ℝ)*(n*sqrt n/log n) = (19/30)*n*sqrt n/log n := by ring
    rw [he] at hmul
    linarith

theorem cube_96699_from_369 (hS : SourceSchoenfeld61) (rh : RiemannHypothesis)
    (hlo : PublishedButheThetaLower) (hhi : PublishedButheThetaUpper)
    {n : ℝ} (hn : 369 ≤ n) :
    (96699/100000:ℝ) * (n^2/log n) < count (n^3) ((n+1)^3) := by
  apply cube_from_theta hS rh hlo hhi (show 45/4 ≤ n by linarith) (by norm_num)
  have h : (96/5:ℝ) ≤ sqrt n := (le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  linarith

theorem cube_96699_from_exp8 (hS : SourceSchoenfeld61) (rh : RiemannHypothesis)
    (hlo : PublishedButheThetaLower) (hhi : PublishedButheThetaUpper)
    {n : ℝ} (hn : exp 8 ≤ n) :
    (96699/100000:ℝ) * (n^2/log n) < count (n^3) ((n+1)^3) := by
  apply cube_96699_from_369 hS rh hlo hhi
  have h := sum_le_exp_of_nonneg (show (0:ℝ) ≤ 8 by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h
  linarith

#print axioms theta_sub_le_strict_count
#print axioms buthe_profile
#print axioms schoenfeld_profile
#print axioms cube_96699_from_369
#print axioms cube_96699_from_exp8
#check RH080.Dual.kernel_compact_obstruction
end
end FreshCubes
