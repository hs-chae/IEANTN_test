import OcticFourierMollifier

/-! The larger finite Mangoldt population needed for the actual mollification.
It is not silently truncated at the smaller original support. -/
namespace RHOcticPush.PopulationLimit
open Real Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Convolution
open RHOcticPush.Mollifier RHOcticPush.FourierMollifier
set_option maxHeartbeats 0

theorem smoothKernel_compact (j : ℕ) : HasCompactSupport (smoothKernel j) :=
  ((bump j).hasCompactSupport_normed (μ := volume)).convolution (lsmul ℝ ℝ) kernel_compact

theorem smoothKernel_support (j : ℕ) :
    Function.support (smoothKernel j) ⊆ Set.Ioo (-2 : ℝ) 2 := by
  intro u hu
  have hm := support_convolution_subset (L := lsmul ℝ ℝ) (μ := volume) hu
  rcases hm with ⟨v, hv, w, hw, rfl⟩
  rw [(bump j).support_normed_eq] at hv
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hv
  have hr : (bump j).rOut ≤ 1 := by
    change 1 / ((j : ℝ) + 1) ≤ 1
    apply (div_le_one (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg j)
  have hv' := abs_lt.mp (hv.trans_le hr)
  have hw' := kernel_support hw
  change -2 < v + w ∧ v + w < 2
  exact ⟨by linarith [hw'.1], by linarith [hw'.2]⟩

lemma kernel_nonzero_between {C L : ℝ} (hδ : 0 < EvenKernel.δ C L)
    {k : ℕ} (hk : k ≠ 0)
    (hkernel : EvenKernel.kernel 4 ((Real.log k - L) / EvenKernel.δ C L) ≠ 0) :
    EvenKernel.a C L < (k : ℝ) ∧ (k : ℝ) < EvenKernel.b C L := by
  have hx := kernel_support hkernel
  have hlo := (lt_div_iff₀ hδ).mp hx.1
  have hhi := (div_lt_iff₀ hδ).mp hx.2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  constructor
  · calc
      EvenKernel.a C L < Real.exp (Real.log (k : ℝ)) := by
        apply Real.exp_lt_exp.mpr
        linarith
      _ = _ := Real.exp_log hk0
  · calc
      (k : ℝ) = Real.exp (Real.log (k : ℝ)) := (Real.exp_log hk0).symm
      _ < EvenKernel.b C L := by
        apply Real.exp_lt_exp.mpr
        linarith

theorem original_population_eq_larger_range {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) {N : ℕ} (hN : ⌊EvenKernel.b C L⌋₊ + 1 ≤ N) :
    EvenKernel.mangoldtPopulation 4 C L =
      ∑ k ∈ Finset.range N,
        EvenKernel.kernel 4 ((Real.log k - L) / EvenKernel.δ C L) *
          ((ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k) := by
  classical
  unfold EvenKernel.mangoldtPopulation
  apply Finset.sum_subset
  · intro k hk
    have hm := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    exact Finset.mem_range.mpr (hm.trans_le hN)
  · intro k hk hnot
    by_cases hk0 : k = 0
    · simp [hk0]
    by_cases hz : EvenKernel.kernel 4 ((Real.log k - L) / EvenKernel.δ C L) = 0
    · simp [hz]
    have hab := kernel_nonzero_between hδ hk0 hz
    have hkfloor : k ≤ ⌊EvenKernel.b C L⌋₊ := (Nat.le_floor_iff' hk0).mpr hab.2.le
    exact (hnot (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hab⟩)).elim

noncomputable def populationCap (C L : ℝ) : ℕ := ⌊Real.exp (L + 2 * EvenKernel.δ C L)⌋₊ + 1

noncomputable def smoothPopulation (j : ℕ) (C L : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (populationCap C L),
    smoothKernel j ((Real.log k - L) / EvenKernel.δ C L) *
      ((ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k)

theorem smoothPopulation_tends {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) :
    Tendsto (fun j : ℕ => smoothPopulation j C L) atTop
      (𝓝 (EvenKernel.mangoldtPopulation 4 C L)) := by
  have hN : ⌊EvenKernel.b C L⌋₊ + 1 ≤ populationCap C L := by
    unfold populationCap
    apply Nat.add_le_add_right
    apply Nat.floor_le_floor
    apply Real.exp_le_exp.mpr
    linarith
  rw [original_population_eq_larger_range hδ hN]
  exact finite_population_limit _ _ _ _

/-- The fixed larger population is exactly the complete smooth prime-power sum;
the numerical cap does not discard any supported natural-number contribution. -/
theorem smoothPopulation_eq_tsum (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) :
    smoothPopulation j C L =
      ∑' k : ℕ, smoothKernel j ((Real.log k - L) / EvenKernel.δ C L) *
        ((ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k) := by
  classical
  symm
  apply tsum_eq_sum
  intro k hk
  by_cases hk0 : k = 0
  · simp [hk0]
  by_cases hz : smoothKernel j ((Real.log k - L) / EvenKernel.δ C L) = 0
  · simp [hz]
  have hsupport := smoothKernel_support j hz
  have hhi := (div_lt_iff₀ hδ).mp hsupport.2
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  have hb : (k : ℝ) < Real.exp (L + 2 * EvenKernel.δ C L) := by
    calc (k : ℝ) = Real.exp (Real.log (k : ℝ)) := (Real.exp_log hkpos).symm
         _ < _ := Real.exp_lt_exp.mpr (by linarith)
  have hfloor : k ≤ ⌊Real.exp (L + 2 * EvenKernel.δ C L)⌋₊ :=
    (Nat.le_floor_iff' hk0).mpr hb.le
  apply (hk (Finset.mem_range.mpr ?_)).elim
  unfold populationCap
  omega

#print axioms smoothKernel_support
#print axioms original_population_eq_larger_range
#print axioms smoothPopulation_tends
#print axioms smoothPopulation_eq_tsum
end RHOcticPush.PopulationLimit
