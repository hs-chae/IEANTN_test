import OcticBPTInfinite

/-! Exact lower-endpoint BPT transport. This preserves the actual remainder at
cutoff12, where the proved zero count vanishes; no artificial R log12 cost is
added. Absolute values are handled by the existing smooth-majorant construction.
All source and infinite-tail hypotheses remain explicit until specialization. -/
namespace RHOcticPush.BoxZero
open Real Set MeasureTheory Filter
open RHLimit.BPTZeroCount RHLimit.AbsoluteStieltjes
set_option maxHeartbeats 0

theorem finite_remainder_exact_endpoint_bound (h : PublishedBound) {a b : ℝ}
    (ha : 2 * Real.pi ≤ a) (hab : a ≤ b) {φ φ' : ℝ → ℝ}
    (hd : ∀ t ∈ uIcc a b, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (uIcc a b)) :
    |IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ φ ρ.im) -
      (∫ t in a..b, φ t * density t)| ≤
      (7 / 25) * (|φ b| * Real.log b +
        ∫ t in a..b, |φ' t| * Real.log t) + |φ a| * |remainder a| := by
  have ha1 : 1 ≤ a := by linarith [Real.pi_gt_three]
  have hp (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t := by
    rw [uIcc_of_le hab] at ht
    linarith [ht.1]
  have hlog : ContinuousOn Real.log (uIcc a b) :=
    fun t ht => (Real.continuousAt_log (hp t ht).ne').continuousWithinAt
  have hm : ContinuousOn ZeroCount.v1.rvmMain (uIcc a b) :=
    fun t ht => (main_hasDerivAt (hp t ht)).continuousAt.continuousWithinAt
  have hn := RHContinuation.ZeroCountIntegral.count_integrable (by linarith : 0 ≤ a) hab
  have hir : IntervalIntegrable (fun t => φ' t * remainder t) volume a b :=
    (hn.sub hm.intervalIntegrable).continuousOn_mul hc
  have hj : IntervalIntegrable (fun t => (7 / 25) * (|φ' t| * Real.log t)) volume a b :=
    ((hc.abs.mul hlog).const_mul _).intervalIntegrable
  have hI : |∫ t in a..b, φ' t * remainder t| ≤
      (7 / 25) * ∫ t in a..b, |φ' t| * Real.log t := by
    calc _ ≤ ∫ t in a..b, |φ' t * remainder t| :=
           intervalIntegral.abs_integral_le_integral_abs hab
         _ ≤ ∫ t in a..b, (7 / 25) * (|φ' t| * Real.log t) := by
           apply intervalIntegral.integral_mono_on hab hir.abs hj
           intro t ht
           have hbound := h t (ha.trans ht.1)
           change |remainder t| ≤ _ at hbound
           rw [abs_mul]
           nlinarith [mul_le_mul_of_nonneg_left hbound (abs_nonneg (φ' t))]
         _ = _ := intervalIntegral.integral_const_mul _ _
  rw [finite_remainder ha1 hab hd hc]
  calc _ ≤ |φ b| * |remainder b| + |φ a| * |remainder a| +
      |∫ t in a..b, φ' t * remainder t| := by
        calc _ ≤ |φ b * remainder b - φ a * remainder a| +
            |∫ t in a..b, φ' t * remainder t| := abs_sub _ _
             _ ≤ (|φ b * remainder b| + |φ a * remainder a|) +
                 |∫ t in a..b, φ' t * remainder t| := by gcongr; exact abs_sub _ _
             _ = _ := by rw [abs_mul, abs_mul]
       _ ≤ |φ b| * ((7 / 25) * Real.log b) + |φ a| * |remainder a| +
           (7 / 25) * (∫ t in a..b, |φ' t| * Real.log t) := by
             apply add_le_add _ hI
             exact add_le_add (mul_le_mul_of_nonneg_left
               (h b (ha.trans hab)) (abs_nonneg _)) le_rfl
       _ = _ := by ring


lemma majorant_exact_endpoint_bound (h : PublishedBound) {a b ε : ℝ}
    (ha : 2 * Real.pi ≤ a) (hab : a ≤ b) (hε : 0 < ε) {f f' : ℝ → ℝ}
    (hd : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (uIcc a b)) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ |f ρ.im|) ≤
      (∫ t in a..b, |f t| * density t) +
      (7 / 25) * (|f b| * Real.log b +
        ∫ t in a..b, |f' t| * Real.log t) + |f a| * |remainder a| +
      ε * ((∫ t in a..b, density t) + (7 / 25) * Real.log b + |remainder a|) := by
  have ha0 : 0 < a := by linarith [Real.pi_pos]
  have hp (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t := by
    rw [uIcc_of_le hab] at ht
    exact ha0.trans_le ht.1
  have hfc : ContinuousOn f (uIcc a b) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hgc := smooth_continuousOn (ε := ε) hfc
  have hgdc := smoothDeriv_continuousOn hε hfc hc
  have hgd : ∀ t ∈ uIcc a b,
      HasDerivAt (smooth ε f) (smoothDeriv ε f f' t) t := by
    intro t ht
    exact smooth_derivative hε (hd t ht)
  have hdensity : ContinuousOn density (uIcc a b) := by
    unfold density
    apply ContinuousOn.div_const
    apply ContinuousOn.log (continuousOn_id.div_const (2 * Real.pi))
    intro t ht
    exact div_ne_zero (hp t ht).ne' (by positivity)
  have hlog : ContinuousOn Real.log (uIcc a b) :=
    fun t ht => (Real.continuousAt_log (hp t ht).ne').continuousWithinAt
  have hlog0 (t : ℝ) (ht : a ≤ t) : 0 ≤ Real.log t := by
    apply Real.log_nonneg
    linarith [Real.pi_gt_three]
  have hsum : IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ |f ρ.im|) ≤
      IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ smooth ε f ρ.im) := by
    let hz := CH2Section7Z.finite_zeros_Ioc (a := a) (b := b) ha0.le
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hz, CH2Section7Z.zetaZeroesSum_eq_sum hz]
    apply Finset.sum_le_sum
    intro ρ hρ
    exact mul_le_mul_of_nonneg_right (smooth_lower ε f ρ.im)
      (CH2Section7Z.zetaOrder_nonneg_of_mem (fun t ht => ha0.trans ht.1)
        ((Set.Finite.mem_toFinset hz).mp hρ))
  have hmain : (∫ t in a..b, smooth ε f t * density t) ≤
      (∫ t in a..b, |f t| * density t) + ε * ∫ t in a..b, density t := by
    calc _ ≤ ∫ t in a..b, (|f t| + ε) * density t := by
           apply intervalIntegral.integral_mono_on hab (hgc.mul hdensity).intervalIntegrable
             ((hfc.abs.add continuousOn_const).mul hdensity).intervalIntegrable
           intro t ht
           exact mul_le_mul_of_nonneg_right (smooth_upper hε.le f t)
             (density_nonneg (ha.trans ht.1))
         _ = _ := by
           simp only [add_mul]
           rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
           · exact (hfc.abs.mul hdensity).intervalIntegrable
           · exact (hdensity.const_mul ε).intervalIntegrable
  have hder : (∫ t in a..b, |smoothDeriv ε f f' t| * Real.log t) ≤
      ∫ t in a..b, |f' t| * Real.log t := by
    apply intervalIntegral.integral_mono_on hab (hgdc.abs.mul hlog).intervalIntegrable
      (hc.abs.mul hlog).intervalIntegrable
    intro t ht
    exact mul_le_mul_of_nonneg_right (smooth_derivative_bound hε f f' t) (hlog0 t ht.1)
  have hb := mul_le_mul_of_nonneg_right (smooth_upper hε.le f b) (hlog0 b hab)
  have haa := mul_le_mul_of_nonneg_right (smooth_upper hε.le f a) (abs_nonneg (remainder a))
  have he := (le_abs_self _).trans (finite_remainder_exact_endpoint_bound h ha hab hgd hgdc)
  rw [abs_of_pos (smooth_pos hε f b), abs_of_pos (smooth_pos hε f a)] at he
  nlinarith

/-- The actual finite absolute-value Stieltjes bound, without differentiability of abs(f). -/
theorem finite_absolute_exact_endpoint_bound (h : PublishedBound) {a b : ℝ}
    (ha : 2 * Real.pi ≤ a) (hab : a ≤ b) {f f' : ℝ → ℝ}
    (hd : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (uIcc a b)) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ |f ρ.im|) ≤
      (∫ t in a..b, |f t| * density t) +
      (7 / 25) * (|f b| * Real.log b +
        ∫ t in a..b, |f' t| * Real.log t) + |f a| * |remainder a| := by
  apply le_of_forall_pos_le_add
  intro η hη
  let A := (∫ t in a..b, density t) + (7 / 25) * Real.log b + |remainder a|
  let ε := η / (|A| + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have he := majorant_exact_endpoint_bound h ha hab hε hd hc
  have hslack : ε * A ≤ η := by
    calc _ ≤ ε * (|A| + 1) :=
           mul_le_mul_of_nonneg_left (by linarith [le_abs_self A]) hε.le
         _ = η := by dsimp [ε]; field_simp
  exact he.trans (by dsimp [A] at hslack; linarith)


#print axioms finite_remainder_exact_endpoint_bound
#print axioms majorant_exact_endpoint_bound
#print axioms finite_absolute_exact_endpoint_bound
end RHOcticPush.BoxZero
