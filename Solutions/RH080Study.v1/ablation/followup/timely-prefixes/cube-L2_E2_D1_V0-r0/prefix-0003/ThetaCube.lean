import Definitions
import QuarticWindow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import CompactDualVerified

/-! Strict-open cube profiles from named published analytic facts.
The imported compact-dual obstruction is separate: none of the count proofs use it. -/
namespace FreshCubes
open Real Finset
open MertensPositive
noncomputable section
set_option maxHeartbeats 0

def SourceSchoenfeld61 : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 2300000000 ≤ x →
    |Chebyshev.theta x - x| < sqrt x * (log x - 2) * log x / (8 * π)

def count (a b : ℝ) : ℝ := (QuarticWindow.primesBetween a b).card

lemma theta_sub_le_strict_count {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Chebyshev.theta b - Chebyshev.theta a ≤ (count a b + 1) * log b := by
  classical
  let S (x : ℝ) := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime
  let D := S b \ S a
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := ha0.trans hab
  have hsub : S a ⊆ S b := by
    intro p hp
    obtain ⟨h, hP⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp0, hpa⟩ := Finset.mem_Ioc.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨hp0, hpa.trans (Nat.floor_le_floor hab)⟩, hP⟩
  have hD (p : ℕ) (hp : p ∈ D) :
      p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
    obtain ⟨hpB, hnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨h, hP⟩ := Finset.mem_filter.mp hpB
    obtain ⟨hp0, hpb⟩ := Finset.mem_Ioc.mp h
    refine ⟨hP, ?_, ?_⟩
    · by_contra! hh
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp0, Nat.le_floor hh⟩, hP⟩)
    · exact (Nat.le_floor_iff hb0).mp hpb
  have hcard : (D.card : ℝ) ≤ count a b + 1 := by
    have hS : D ⊆ insert ⌊b⌋₊ (QuarticWindow.primesBetween a b) := by
      intro p hp
      obtain ⟨hpP, hpa, hpb⟩ := hD p hp
      rcases hpb.lt_or_eq with hlt | he
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
          ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpb, hpP⟩, hpa, hlt⟩)
      · have hh : ⌊b⌋₊ = p := by rw [← he, Nat.floor_natCast]
        exact Finset.mem_insert.mpr (Or.inl hh.symm)
    have hi := (Finset.card_le_card hS).trans (Finset.card_insert_le _ _)
    unfold count
    exact_mod_cast hi
  have hsum : (∑ p ∈ D, log (p : ℝ)) + Chebyshev.theta a = Chebyshev.theta b :=
    Finset.sum_sdiff hsub
  have hlb : 0 ≤ log b := log_nonneg (ha.le.trans hab)
  calc
    _ = ∑ p ∈ D, log (p : ℝ) := by linarith
    _ ≤ ∑ _p ∈ D, log b := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpP, hpa, hpb⟩ := hD p hp
      exact log_le_log (by linarith) hpb
    _ = (D.card : ℝ) * log b := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hlb

lemma log_step {n : ℝ} (hn : 0 < n) : log (n+1) ≤ log n + 1/n := by
  have h := log_le_sub_one_of_pos (show 0 < (n+1)/n by positivity)
  rw [log_div (by positivity : n+1 ≠ 0) hn.ne'] at h
  have he : (n+1)/n-1 = 1/n := by field_simp; ring
  rw [he] at h
  linarith

lemma sqrt_cube {n : ℝ} (hn : 0 ≤ n) : sqrt (n^3) = n * sqrt n := by
  rw [show n^3 = n^2*n by ring, sqrt_mul (sq_nonneg _), sqrt_sq hn]

lemma cube_bridge {n : ℝ} (hn : 2 ≤ n) :
    Chebyshev.theta ((n+1)^3) - Chebyshev.theta (n^3) ≤
      (count (n^3) ((n+1)^3)+1) * (3*log (n+1)) := by
  have ha : 1 < n^3 := lt_of_lt_of_le (by norm_num : (1:ℝ) < 2^3)
    (pow_le_pow_left₀ (by norm_num) hn 3)
  have hb : n^3 ≤ (n+1)^3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  simpa only [log_pow, Nat.cast_ofNat] using theta_sub_le_strict_count ha hb

/-- Explicit profile; no RH required in this finite-slab theorem. -/
theorem buthe_exact (hlo : PublishedButheThetaLower) (hhi : PublishedButheThetaUpper)
    {n : ℝ} (hn : 45/4 ≤ n) (hcap : (n+1)^3 ≤ (10:ℝ)^19) :
    (((n+1)^3-n^3) - (39/20)*(n+1)*sqrt (n+1) + (1/20)*n*sqrt n) /
       (3*log (n+1)) - 1 < count (n^3) ((n+1)^3) := by
  have hn2 : 2 ≤ n := by linarith
  have ha : (1423:ℝ) ≤ n^3 := le_trans (by norm_num : (1423:ℝ) ≤ (45/4)^3)
    (pow_le_pow_left₀ (by norm_num) hn 3)
  have hab : n^3 ≤ (n+1)^3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hL := hlo _ (ha.trans hab) hcap
  have hU := hhi _ (by linarith) (hab.trans hcap)
  rw [sqrt_cube (by positivity : 0 ≤ n+1)] at hL
  rw [sqrt_cube (by linarith : 0 ≤ n)] at hU
  have hu : 0 < 3 * log (n+1) := mul_pos (by norm_num) (log_pos (by linarith))
  suffices (((n+1)^3-n^3) - (39/20)*(n+1)*sqrt (n+1) + (1/20)*n*sqrt n) /
       (3*log (n+1)) < count (n^3) ((n+1)^3) + 1 by linarith
  apply (div_lt_iff₀ hu).mpr
  have hbridge := cube_bridge hn2
  linarith

lemma log_room {n : ℝ} (hn : 45/4 ≤ n) :
    (12/5 : ℝ) ≤ log n ∧ log (n+1) ≤ n/4 := by
  have hd : log (45/4 : ℝ) = log 5 + 2*log 3 - 2*log 2 := by
    rw [show (45/4 : ℝ) = (5*3^2)/2^2 by norm_num, log_div (by norm_num)
      (by norm_num), log_mul (by norm_num) (by norm_num), log_pow, log_pow]
    norm_num
  have hu0 : log (49/4 : ℝ) ≤ 11/4 := by
    have h := log_le_log (by norm_num : (0:ℝ) < 49/4)
      (by norm_num : (49/4:ℝ) ≤ 3^3/2)
    rw [log_div (show (3:ℝ)^3 ≠ 0 by norm_num) (show (2:ℝ) ≠ 0 by norm_num), log_pow] at h
    norm_num at h
    linarith [log_three_lt_d9, log_two_gt_d9]
  constructor
  · have h := log_le_log (by norm_num : (0:ℝ) < 45/4) hn
    linarith [log_five_gt_d9, log_three_gt_d9, log_two_lt_d9]
  · have h := log_le_sub_one_of_pos (show 0 < (n+1)/(49/4) by positivity)
    rw [log_div (by linarith : n+1 ≠ 0) (by norm_num : (49/4:ℝ) ≠ 0)] at h
    linarith

lemma main_room {n : ℝ} (hn : 45/4 ≤ n) :
    (3*log (n+1))*(n^2/log n) ≤ 3*n^2+(5/4)*n := by
  have hn0 : 0 < n := by linarith
  have hL := (log_room hn).1
  have hl0 : 0 < log n := by linarith
  have hU := log_step hn0
  have hT := mul_le_mul_of_nonneg_right hU (sq_nonneg n)
  have hE : (1/n)*n^2 = n := by field_simp
  -- Clear the one positive denominator using a rearrangement.
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hl0).mpr
  rw [add_mul] at hT
  rw [hE] at hT
  nlinarith [mul_le_mul_of_nonneg_left hL (show 0 ≤ (5/4)*n by positivity)]

lemma root_increment {n : ℝ} (hn : 45/4 ≤ n) :
    (n+1)*sqrt (n+1) - n*sqrt n ≤ (8/5)*sqrt n := by
  have hn0 : 0 < n := by linarith
  have hr := sqrt_pos.mpr hn0
  have hsq := sq_sqrt hn0.le
  have hsq' := sq_sqrt (show 0 ≤ n+1 by positivity)
  have hp : sqrt (n+1) * sqrt n ≤ n + 1/2 := by
    nlinarith [sq_nonneg (sqrt (n+1) - sqrt n)]
  apply le_of_mul_le_mul_right _ hr
  calc
    _ = (n+1)*(sqrt (n+1)*sqrt n)-n*n := by
      linear_combination -n * hsq
    _ ≤ (n+1)*(n+1/2)-n*n := by gcongr
    _ ≤ ((8/5)*sqrt n)*sqrt n := by
      nlinarith only [hsq, hn]

theorem buthe_profile (hlo : PublishedButheThetaLower) (hhi : PublishedButheThetaUpper)
    {n : ℝ} (hn : 45/4 ≤ n) (hcap : (n+1)^3 ≤ (10:ℝ)^19) :
    n^2/log n - (19/30)*n*sqrt n/log n < count (n^3) ((n+1)^3) := by
  have hn0 : 0 < n := by linarith
  have hL0 : 0 < log n := by linarith [(log_room hn).1]
  have hU0 : 0 < 3*log (n+1) := by
    exact mul_pos (by norm_num) (log_pos (by linarith))
  have hmain := main_room hn
  have hroom := (log_room hn).2
  have hR : (10/3:ℝ) ≤ sqrt n := by
    apply (le_sqrt (by norm_num) hn0.le).mpr
    linarith
  have hP := mul_le_mul_of_nonneg_right hR (sqrt_nonneg n)
  have hs : (10/3)*sqrt n ≤ n := by nlinarith [sq_sqrt hn0.le]
  have hdiff := root_increment hn
  have hlu : log n ≤ log (n+1) := log_le_log hn0 (by linarith)
  have hdebt : (19/10)*n*sqrt n ≤ (3*log (n+1))*((19/30)*n*sqrt n/log n) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hL0).mpr
    have hh := mul_le_mul_of_nonneg_right hlu (show 0 ≤ (19/10)*n*sqrt n by positivity)
    linear_combination hh
  apply lt_of_le_of_lt _ (buthe_exact hlo hhi hn hcap)
  rw [le_sub_iff_add_le]
  apply (le_div_iff₀ hU0).mpr
  simp only [add_mul, sub_mul, one_mul]
  rw [mul_comm (n^2/log n), mul_comm ((19/30)*n*sqrt n/log n)]
  nlinarith only [hmain, hdebt, hroom, hs, hdiff, hn0]
end
end FreshCubes
