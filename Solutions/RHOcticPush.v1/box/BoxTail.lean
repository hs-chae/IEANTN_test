import Mathlib
import CLogMoment

namespace RHOcticPush.BoxTail
open Real Finset CLogMoment
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

/-- A finite telescoping block exposes positive information discarded at128. -/
def tailCorrection : ℚ := lower 128 / 8 * (1 / 129 ^ 2 - 1 / 4097 ^ 2)
def improvedUpper : ℚ := finalUpper - tailCorrection

lemma inverse_square_difference {x : ℝ} (hx : 0 < x) :
    1 / x ^ 2 - 1 / (x + 1) ^ 2 ≤ 2 / x ^ 3 := by
  have hp : 0 < x^3 * (x+1)^2 := by positivity
  apply (mul_le_mul_iff_left₀ hp).mp
  field_simp
  nlinarith [sq_nonneg x]

lemma tail_term_lower {n : ℕ} (hn : 129 ≤ n) :
    (lower 128 : ℝ) / 8 * (1 / (n : ℝ)^2 - 1 / ((n : ℝ)+1)^2) ≤ qTerm n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast (show 2≤n by omega)
  have hl0 : (0:ℝ) ≤ lower 128 := by
    have h := (sample_interval (n:=128) (by norm_num) (by norm_num)).1
    have hnum : (0:ℚ) ≤ lower 128 := by decide +kernel
    exact_mod_cast hnum
  have hl : (lower 128 : ℝ) ≤ Real.log n :=
    (sample_interval (n:=128) (by norm_num) (by norm_num)).1.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast (show 128≤n by omega)))
  have hd : 0 < (n : ℝ) * (4*n^2-1) := by
    apply mul_pos hn0
    nlinarith [sq_nonneg (n:ℝ)]
  have hd' : (n : ℝ) * (4*n^2-1) ≤ 4*n^3 := by nlinarith
  have hh : (lower 128 : ℝ) / (4*(n : ℝ)^3) ≤ qTerm n := by
    rw [qTerm, if_neg (show ¬n<2 by omega)]
    apply (div_le_div_iff₀ (by positivity) hd).mpr
    have h1 := mul_le_mul_of_nonneg_left hd' hl0
    have h2 := mul_le_mul_of_nonneg_right hl (show 0≤4*(n:ℝ)^3 by positivity)
    linarith
  have hdiff := mul_le_mul_of_nonneg_left (inverse_square_difference hn0)
    (show 0 ≤ (lower 128 : ℝ)/8 by positivity)
  have he : (lower 128 : ℝ)/8 * (2/(n:ℝ)^3) =
      (lower 128 : ℝ)/(4*(n:ℝ)^3) := by ring
  rw [he] at hdiff
  exact hdiff.trans hh

lemma finite_tail_lower : (tailCorrection : ℝ) ≤
    ∑ n ∈ Ico (129:ℕ) 4097, qTerm n := by
  calc
    (tailCorrection : ℝ) = (lower 128 : ℝ)/8 *
        (1/(129:ℝ)^2-1/(4097:ℝ)^2) := by norm_num [tailCorrection]
    _ = (lower 128 : ℝ)/8 * ∑ n ∈ Ico (129:ℕ) 4097,
        (1/(n:ℝ)^2 - 1/((n:ℝ)+1)^2) := by
      congr 1
      have h := Finset.sum_Ico_sub (fun n : ℕ => -(1/(n:ℝ)^2))
        (show 129≤4097 by norm_num)
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, neg_sub_neg] at h
      exact h.symm
    _ = ∑ n ∈ Ico (129:ℕ) 4097, (lower 128 : ℝ)/8 *
        (1/(n:ℝ)^2 - 1/((n:ℝ)+1)^2) := by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun n hn => tail_term_lower (Finset.mem_Ico.mp hn).1

lemma prefix_lower : (qLower : ℝ) ≤ ∑ n ∈ samples, qTerm n := by
  simp only [qLower, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]
  apply Finset.sum_le_sum
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn'.1
  have hl := (sample_interval hn'.1 hn'.2).1
  simp only [qTerm, if_neg (show ¬n<2 by omega)]
  apply div_le_div_of_nonneg_right hl
  nlinarith [sq_nonneg (n:ℝ)]

/-- Actual infinite series lower bound; finite truncation pays no unproved tail. -/
theorem q_lower_improved : (qLower : ℝ) + tailCorrection ≤ q := by
  have hunion : samples ∪ Ico (129:ℕ) 4097 = Icc 2 4096 := by
    ext n
    simp only [mem_union, samples, mem_Icc, mem_Ico]
    omega
  have hdis : Disjoint samples (Ico (129:ℕ) 4097) := by
    rw [Finset.disjoint_left]
    intro n hn hm
    have h1 := (Finset.mem_Icc.mp hn).2
    have h2 := (Finset.mem_Ico.mp hm).1
    omega
  calc
    (qLower : ℝ) + tailCorrection ≤ (∑ n ∈ samples, qTerm n) +
        ∑ n ∈ Ico (129:ℕ) 4097, qTerm n := add_le_add prefix_lower finite_tail_lower
    _ = ∑ n ∈ Icc 2 4096, qTerm n := by rw [← Finset.sum_union hdis, hunion]
    _ ≤ q := qTerm_summable.sum_le_tsum _ (fun n _ => qTerm_nonneg n)

#print axioms q_lower_improved
end RHOcticPush.BoxTail
