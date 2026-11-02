import FKS2Scalar.ExpCertificate

namespace FKS2Scalar

def gridDown (x : Rat) : Rat := (⌊x * 10 ^ 18⌋ : Int) / (10 ^ 18 : Rat)
def expLo (x : Rat) := gridDown ((expPoly x - 1 / 10 ^ 16) ^ 32)
def expHi (x : Rat) := gridDown ((expPoly x + 1 / 10 ^ 16) ^ 32) + 1 / 10 ^ 18
def x1 (k : Nat) : Rat := 30 * (1 / (k : Rat) - 1 / 3)
def x2lo (k : Nat) : Rat := (44 * (6931471808 / 10 ^ 10)) * (1 / (k : Rat) - 1 / 3)
def x2hi (k : Nat) : Rat := (44 * (6931471803 / 10 ^ 10)) * (1 / (k : Rat) - 1 / 3)
def s1lo : Rat := ∑ k ∈ Finset.Icc 3 43, expLo (x1 k)
def s1hi : Rat := ∑ k ∈ Finset.Icc 3 43, expHi (x1 k)
def s2lo : Rat := ∑ k ∈ Finset.Icc 3 44, expLo (x2lo k)
def s2hi : Rat := ∑ k ∈ Finset.Icc 3 44, expHi (x2hi k)
def uLo : Rat := 430760200111 / 10 ^ 12
def uHi : Rat := 430760200112 / 10 ^ 12
def zLo : Rat := 2321477238940 / 10 ^ 12
def zHi : Rat := 2321477238941 / 10 ^ 12

def nuLo : Rat :=
  (1 / 121.096) * uLo ^ 3 * expLo (2 * zLo) *
    ((1 + 1.93378e-8) * 30 * expLo (-15) +
      ((1 + 1.93378e-8) * max s1lo s2lo) * 30 * expLo (-20))
def nuHi : Rat :=
  (1 / 121.096) * uHi ^ 3 * expHi (2 * zHi) *
    ((1 + 1.93378e-8) * 30 * expHi (-15) +
      ((1 + 1.93378e-8) * max s1hi s2hi) * 30 * expHi (-20))

theorem sum1_checks : ∀ k ∈ Finset.Icc 3 43,
    expCheck (x1 k) (expLo (x1 k)) (expHi (x1 k)) = true := by
  native_decide

theorem sum2_checks : ∀ k ∈ Finset.Icc 3 44,
    expCheck (x2lo k) (expLo (x2lo k)) (expHi (x2lo k)) = true ∧
    expCheck (x2hi k) (expLo (x2hi k)) (expHi (x2hi k)) = true := by
  native_decide

theorem sum1_bounds : (s1lo : ℝ) ≤ sum1 ∧ sum1 ≤ (s1hi : ℝ) := by
  simp only [s1lo, s1hi, Rat.cast_sum, sum1]
  constructor
  · apply Finset.sum_le_sum
    intro k hk
    have h := (expCheck_sound (sum1_checks k hk)).1
    simpa [x1] using h
  · apply Finset.sum_le_sum
    intro k hk
    have h := (expCheck_sound (sum1_checks k hk)).2
    simpa [x1] using h

theorem x2_bounds (k : Nat) (hk : k ∈ Finset.Icc 3 44) :
    (x2lo k : ℝ) ≤ (44 * Real.log 2) * ((1 : ℝ) / k - 1 / 3) ∧
    (44 * Real.log 2) * ((1 : ℝ) / k - 1 / 3) ≤ (x2hi k : ℝ) := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hkpos : (0 : ℝ) < k := by linarith
  have hd : (1 : ℝ) / k - 1 / 3 ≤ 0 := by
    have hi : (1 : ℝ) / k ≤ 1 / 3 := (div_le_div_iff₀ hkpos (by norm_num)).2 (by linarith)
    linarith
  have hl := mul_le_mul_of_nonpos_right (le_of_lt Real.log_two_lt_d9) hd
  have hu := mul_le_mul_of_nonpos_right (le_of_lt Real.log_two_gt_d9) hd
  simp only [x2lo, x2hi, Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_pow, Rat.cast_one]
  constructor <;> nlinarith

theorem sum2_bounds : (s2lo : ℝ) ≤ sum2 ∧ sum2 ≤ (s2hi : ℝ) := by
  simp only [s2lo, s2hi, Rat.cast_sum, sum2]
  constructor
  · apply Finset.sum_le_sum
    intro k hk
    exact (expCheck_sound (sum2_checks k hk).1).1.trans
      (Real.exp_le_exp.mpr (x2_bounds k hk).1)
  · apply Finset.sum_le_sum
    intro k hk
    exact (Real.exp_le_exp.mpr (x2_bounds k hk).2).trans
      (expCheck_sound (sum2_checks k hk).2).2

theorem root_bounds :
    (uLo : ℝ) ≤ Real.sqrt (5.5666305 / 30) ∧
    Real.sqrt (5.5666305 / 30) ≤ (uHi : ℝ) ∧
    (zLo : ℝ) ≤ Real.sqrt (30 / 5.5666305) ∧
    Real.sqrt (30 / 5.5666305) ≤ (zHi : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    norm_num [uLo]
  · apply Real.sqrt_le_iff.mpr
    norm_num [uHi]
  · apply Real.le_sqrt_of_sq_le
    norm_num [zLo]
  · apply Real.sqrt_le_iff.mpr
    norm_num [zHi]

theorem z_exp_checks :
    expCheck (2 * zLo) (expLo (2 * zLo)) (expHi (2 * zLo)) = true ∧
    expCheck (2 * zHi) (expLo (2 * zHi)) (expHi (2 * zHi)) = true ∧
    expCheck (-15) (expLo (-15)) (expHi (-15)) = true ∧
    expCheck (-20) (expLo (-20)) (expHi (-20)) = true := by
  native_decide

theorem target_enclosure : (nuLo : ℝ) ≤ exactTarget ∧ exactTarget ≤ (nuHi : ℝ) := by
  have hs1 := sum1_bounds
  have hs2 := sum2_bounds
  have hr := root_bounds
  have he15 := expCheck_sound z_exp_checks.2.2.1
  have he20 := expCheck_sound z_exp_checks.2.2.2
  simp only [Rat.cast_neg, Rat.cast_ofNat] at he15 he20
  have heL := (expCheck_sound z_exp_checks.1).1
  have heU := (expCheck_sound z_exp_checks.2.1).2
  simp only [Rat.cast_mul, Rat.cast_ofNat] at heL heU
  have hzL : (expLo (2 * zLo) : ℝ) ≤ Real.exp (2 * Real.sqrt (30 / 5.5666305)) :=
    heL.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2.2.1 (by norm_num)))
  have hzU : Real.exp (2 * Real.sqrt (30 / 5.5666305)) ≤ (expHi (2 * zHi) : ℝ) :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2.2.2 (by norm_num))).trans heU
  have hc : (0 : Rat) ≤ uLo ∧ 0 ≤ expLo (2 * zLo) ∧ 0 ≤ expLo (-15) ∧
      0 ≤ expLo (-20) ∧ 0 ≤ s1lo ∧ 0 ≤ s2lo := by native_decide
  have hn0 : (0 : ℝ) ≤ (uLo : ℝ) := by exact_mod_cast hc.1
  have hn1 : (0 : ℝ) ≤ (expLo (2 * zLo) : ℝ) := by exact_mod_cast hc.2.1
  have hn2 : (0 : ℝ) ≤ (expLo (-15) : ℝ) := by exact_mod_cast hc.2.2.1
  have hn3 : (0 : ℝ) ≤ (expLo (-20) : ℝ) := by exact_mod_cast hc.2.2.2.1
  have hn4 : (0 : ℝ) ≤ (s1lo : ℝ) := by exact_mod_cast hc.2.2.2.2.1
  have hn5 : (0 : ℝ) ≤ (s2lo : ℝ) := by exact_mod_cast hc.2.2.2.2.2
  have hsum1 : (0 : ℝ) ≤ sum1 := hn4.trans hs1.1
  have hsum2 : (0 : ℝ) ≤ sum2 := hn5.trans hs2.1
  have hnu : (0 : ℝ) ≤ (uHi : ℝ) := (Real.sqrt_nonneg _).trans hr.2.1
  have hne : (0 : ℝ) ≤ (expHi (2 * zHi) : ℝ) := (Real.exp_nonneg _).trans hzU
  have hns1 : (0 : ℝ) ≤ (s1hi : ℝ) := hsum1.trans hs1.2
  have hns2 : (0 : ℝ) ≤ (s2hi : ℝ) := hsum2.trans hs2.2
  rw [target_normalization]
  unfold normalized nuLo nuHi
  push_cast
  constructor
  · gcongr
    all_goals
      first
      | exact hr.1
      | exact hzL
      | exact he15.1
      | exact he20.1
      | exact hs1.1
      | exact hs2.1
  · gcongr
    all_goals
      first
      | exact hr.2.1
      | exact hzU
      | exact he15.2
      | exact he20.2
      | exact hs1.2
      | exact hs2.2

end FKS2Scalar
