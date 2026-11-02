import FKS2Scalar.Result

namespace FKS2Scalar

/-- Literal decoding uses the very same conversion as selected source execution. -/
def literalValue (s : String) : Rat := ((decimal s).bind round64).getD 0
def roundedR := literalValue "5.5666305"
def roundedAlpha := literalValue "0.0000000193378"
def roundedD := literalValue "121.096"
def roundedLog2 := literalValue "0.6931471805599453"
def aLo : Rat := min (1 + 1.93378e-8) (1 + roundedAlpha)
def aHi : Rat := max (1 + 1.93378e-8) (1 + roundedAlpha)
def dLo : Rat := min 121.096 roundedD
def dHi : Rat := max 121.096 roundedD

noncomputable def sum2For (lg : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 3 44, Real.exp ((44 * lg) * ((1 : ℝ) / (k : ℕ) - 1 / 3))

noncomputable def targetFor (r a d lg : ℝ) : ℝ :=
  (1 / d) * Real.sqrt (r / 30) ^ 3 * Real.exp (2 * Real.sqrt (30 / r)) *
    (a * 30 * Real.exp (-15) + (a * max sum1 (sum2For lg)) * 30 * Real.exp (-20))

/-- Exact transcendental expression after C literal conversion, before any arithmetic rounding. -/
noncomputable def constantTarget : ℝ :=
  targetFor roundedR (1 + (roundedAlpha : ℝ)) roundedD roundedLog2

/-- Same selected AST with exact rational arithmetic and binary64-rounded literals.
This is a proof-side reference execution, not another executable workload. -/
def idealQ : Rat := (executeWith some selectedAST).getD 0

def wideLo : Rat :=
  (1 / dHi) * uLo ^ 3 * expLo (2 * zLo) *
    (aLo * 30 * expLo (-15) + (aLo * max s1lo s2lo) * 30 * expLo (-20))
def wideHi : Rat :=
  (1 / dLo) * uHi ^ 3 * expHi (2 * zHi) *
    (aHi * 30 * expHi (-15) + (aHi * max s1hi s2hi) * 30 * expHi (-20))

def E_constants : Rat := 3 / 10 ^ 16
def E_approximation : Rat := 3 / 10 ^ 16
def E_roundoff : Rat := 4 / 10 ^ 16

theorem ideal_execution : executeWith some selectedAST = some idealQ := by
  native_decide

theorem roundoff_certificate : |q - idealQ| ≤ E_roundoff := by
  native_decide

theorem budget_certificate : wideHi - wideLo ≤ E_constants ∧
    idealQ - E_approximation ≤ wideLo ∧ wideHi ≤ idealQ + E_approximation ∧
    E_constants + E_approximation + E_roundoff = E := by
  native_decide

theorem sum2For_bounds (lg : ℝ) (hlg : 0.6931471803 ≤ lg ∧ lg ≤ 0.6931471808) :
    (s2lo : ℝ) ≤ sum2For lg ∧ sum2For lg ≤ (s2hi : ℝ) := by
  have harg (k : Nat) (hk : k ∈ Finset.Icc 3 44) :
      (x2lo k : ℝ) ≤ (44 * lg) * ((1 : ℝ) / k - 1 / 3) ∧
      (44 * lg) * ((1 : ℝ) / k - 1 / 3) ≤ (x2hi k : ℝ) := by
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by linarith
    have hd : (1 : ℝ) / k - 1 / 3 ≤ 0 := by
      have hi : (1 : ℝ) / k ≤ 1 / 3 := (div_le_div_iff₀ hkpos (by norm_num)).2 (by linarith)
      linarith
    have hl := mul_le_mul_of_nonpos_right hlg.2 hd
    have hu := mul_le_mul_of_nonpos_right hlg.1 hd
    simp only [x2lo, x2hi, Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_pow, Rat.cast_one]
    constructor <;> nlinarith
  simp only [s2lo, s2hi, Rat.cast_sum, sum2For]
  constructor
  · apply Finset.sum_le_sum
    intro k hk
    exact (expCheck_sound (sum2_checks k hk).1).1.trans (Real.exp_le_exp.mpr (harg k hk).1)
  · apply Finset.sum_le_sum
    intro k hk
    exact (Real.exp_le_exp.mpr (harg k hk).2).trans (expCheck_sound (sum2_checks k hk).2).2

theorem for_enclosure (r a d lg : ℝ)
    (hr : (uLo : ℝ) ≤ Real.sqrt (r / 30) ∧ Real.sqrt (r / 30) ≤ (uHi : ℝ) ∧
      (zLo : ℝ) ≤ Real.sqrt (30 / r) ∧ Real.sqrt (30 / r) ≤ (zHi : ℝ))
    (ha : (aLo : ℝ) ≤ a ∧ a ≤ (aHi : ℝ))
    (hd : (dLo : ℝ) ≤ d ∧ d ≤ (dHi : ℝ))
    (hlg : 0.6931471803 ≤ lg ∧ lg ≤ 0.6931471808) :
    (wideLo : ℝ) ≤ targetFor r a d lg ∧ targetFor r a d lg ≤ (wideHi : ℝ) := by
  have hs1 := sum1_bounds
  have hs2 := sum2For_bounds lg hlg
  have he15 := expCheck_sound z_exp_checks.2.2.1
  have he20 := expCheck_sound z_exp_checks.2.2.2
  simp only [Rat.cast_neg, Rat.cast_ofNat] at he15 he20
  have heL := (expCheck_sound z_exp_checks.1).1
  have heU := (expCheck_sound z_exp_checks.2.1).2
  simp only [Rat.cast_mul, Rat.cast_ofNat] at heL heU
  have hzL : (expLo (2 * zLo) : ℝ) ≤ Real.exp (2 * Real.sqrt (30 / r)) :=
    heL.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2.2.1 (by norm_num)))
  have hzU : Real.exp (2 * Real.sqrt (30 / r)) ≤ (expHi (2 * zHi) : ℝ) :=
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
  have hsum2 : (0 : ℝ) ≤ sum2For lg := hn5.trans hs2.1
  have hnu : (0 : ℝ) ≤ (uHi : ℝ) := (Real.sqrt_nonneg _).trans hr.2.1
  have hne : (0 : ℝ) ≤ (expHi (2 * zHi) : ℝ) := (Real.exp_nonneg _).trans hzU
  have hns1 : (0 : ℝ) ≤ (s1hi : ℝ) := hsum1.trans hs1.2
  have hns2 : (0 : ℝ) ≤ (s2hi : ℝ) := hsum2.trans hs2.2
  have ha0 : (0 : ℝ) ≤ (aLo : ℝ) := by
    have h : (0 : Rat) ≤ aLo := by native_decide
    exact_mod_cast h
  have hap : (0 : ℝ) ≤ a := ha0.trans ha.1
  have hah : (0 : ℝ) ≤ (aHi : ℝ) := hap.trans ha.2
  have hd0 : (0 : ℝ) < (dLo : ℝ) := by
    have h : (0 : Rat) < dLo := by native_decide
    exact_mod_cast h
  have hdp : (0 : ℝ) < d := hd0.trans_le hd.1
  have hdh : (0 : ℝ) < (dHi : ℝ) := hdp.trans_le hd.2
  have hil : (1 : ℝ) / (dHi : ℝ) ≤ 1 / d := one_div_le_one_div_of_le hdp hd.2
  have hih : (1 : ℝ) / d ≤ 1 / (dLo : ℝ) := one_div_le_one_div_of_le hd0 hd.1
  unfold targetFor wideLo wideHi
  push_cast
  constructor
  · gcongr
    all_goals
      first
      | exact hil
      | exact ha.1
      | exact hr.1
      | exact hzL
      | exact he15.1
      | exact he20.1
      | exact hs1.1
      | exact hs2.1
  · gcongr
    all_goals
      first
      | exact hih
      | exact ha.2
      | exact hr.2.1
      | exact hzU
      | exact he15.2
      | exact he20.2
      | exact hs1.2
      | exact hs2.2

theorem original_in_wide : (wideLo : ℝ) ≤ exactTarget ∧ exactTarget ≤ (wideHi : ℝ) := by
  have hc : aLo ≤ (1 + 1.93378e-8 : Rat) ∧ (1 + 1.93378e-8 : Rat) ≤ aHi ∧
      dLo ≤ (121.096 : Rat) ∧ (121.096 : Rat) ≤ dHi := by native_decide
  rw [target_normalization]
  apply for_enclosure 5.5666305 (1 + 1.93378e-8) 121.096 (Real.log 2) root_bounds
  · constructor
    · simpa using (Rat.cast_le (K := ℝ)).2 hc.1
    · simpa using (Rat.cast_le (K := ℝ)).2 hc.2.1
  · constructor
    · simpa using (Rat.cast_le (K := ℝ)).2 hc.2.2.1
    · simpa using (Rat.cast_le (K := ℝ)).2 hc.2.2.2
  · exact ⟨Real.log_two_gt_d9.le, Real.log_two_lt_d9.le⟩

theorem rounded_in_wide : (wideLo : ℝ) ≤ constantTarget ∧ constantTarget ≤ (wideHi : ℝ) := by
  have hc : aLo ≤ 1 + roundedAlpha ∧ 1 + roundedAlpha ≤ aHi ∧
      dLo ≤ roundedD ∧ roundedD ≤ dHi ∧
      (6931471803 / 10 ^ 10 : Rat) ≤ roundedLog2 ∧
      roundedLog2 ≤ (6931471808 / 10 ^ 10 : Rat) ∧
      uLo ^ 2 ≤ roundedR / 30 ∧ roundedR / 30 ≤ uHi ^ 2 ∧
      zLo ^ 2 ≤ 30 / roundedR ∧ 30 / roundedR ≤ zHi ^ 2 := by native_decide
  have hr : (uLo : ℝ) ≤ Real.sqrt ((roundedR : ℝ) / 30) ∧
      Real.sqrt ((roundedR : ℝ) / 30) ≤ (uHi : ℝ) ∧
      (zLo : ℝ) ≤ Real.sqrt (30 / (roundedR : ℝ)) ∧
      Real.sqrt (30 / (roundedR : ℝ)) ≤ (zHi : ℝ) := by
    refine ⟨Real.le_sqrt_of_sq_le ?_, Real.sqrt_le_iff.mpr ⟨?_, ?_⟩,
      Real.le_sqrt_of_sq_le ?_, Real.sqrt_le_iff.mpr ⟨?_, ?_⟩⟩
    · simpa using (Rat.cast_le (K := ℝ)).2 hc.2.2.2.2.2.2.1
    · norm_num [uHi]
    · simpa using (Rat.cast_le (K := ℝ)).2 hc.2.2.2.2.2.2.2.1
    · simpa using (Rat.cast_le (K := ℝ)).2 hc.2.2.2.2.2.2.2.2.1
    · norm_num [zHi]
    · simpa using (Rat.cast_le (K := ℝ)).2 hc.2.2.2.2.2.2.2.2.2
  apply for_enclosure roundedR (1 + (roundedAlpha : ℝ)) roundedD roundedLog2 hr
  · constructor
    · simpa using (Rat.cast_le (K := ℝ)).2 hc.1
    · simpa using (Rat.cast_le (K := ℝ)).2 hc.2.1
  · exact ⟨(Rat.cast_le (K := ℝ)).2 hc.2.2.1, (Rat.cast_le (K := ℝ)).2 hc.2.2.2.1⟩
  · constructor
    · have h := (Rat.cast_le (K := ℝ)).2 hc.2.2.2.2.1
      norm_num at h ⊢
      exact h
    · have h := (Rat.cast_le (K := ℝ)).2 hc.2.2.2.2.2.1
      norm_num at h ⊢
      exact h

theorem constants_error : |constantTarget - exactTarget| ≤ (E_constants : ℝ) := by
  have hb : (wideHi : ℝ) - (wideLo : ℝ) ≤ (E_constants : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).2 budget_certificate.1
  rw [abs_le]
  constructor <;> linarith [original_in_wide.1, original_in_wide.2,
    rounded_in_wide.1, rounded_in_wide.2]

theorem approximation_error : |(idealQ : ℝ) - constantTarget| ≤ (E_approximation : ℝ) := by
  have hl : (idealQ : ℝ) - (E_approximation : ℝ) ≤ (wideLo : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).2 budget_certificate.2.1
  have hu : (wideHi : ℝ) ≤ (idealQ : ℝ) + (E_approximation : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).2 budget_certificate.2.2.1
  rw [abs_le]
  constructor <;> linarith [rounded_in_wide.1, rounded_in_wide.2]

theorem budget_forward_error : |(q : ℝ) - exactTarget| ≤ (E : ℝ) := by
  have hround : |(q : ℝ) - (idealQ : ℝ)| ≤ (E_roundoff : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).2 roundoff_certificate
  have hsum : (E_constants : ℝ) + (E_approximation : ℝ) + (E_roundoff : ℝ) = (E : ℝ) := by
    exact_mod_cast budget_certificate.2.2.2
  have h1 := abs_le.mp hround
  have h2 := abs_le.mp approximation_error
  have h3 := abs_le.mp constants_error
  rw [abs_le]
  constructor <;> linarith

end FKS2Scalar
