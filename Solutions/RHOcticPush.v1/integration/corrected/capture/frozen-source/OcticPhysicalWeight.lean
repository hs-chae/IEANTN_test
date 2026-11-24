import OcticPopulationLimit
import OcticGeometry

/-! Actual compact smooth weights eligible for the independently specified
Mellin explicit formula. No explicit-formula conclusion is assumed or proved
in this file: it proves admissibility and the exact physical prime sum. -/
namespace RHOcticPush.PhysicalWeight
open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open RHOcticPush.Mollifier RHOcticPush.PopulationLimit
set_option maxHeartbeats 0

noncomputable def logWeight (j : ℕ) (C L t : ℝ) : ℝ :=
  if 0 < t then smoothKernel j ((Real.log t - L) / EvenKernel.δ C L) / Real.sqrt t else 0

theorem logWeight_support (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) :
    Function.support (logWeight j C L) ⊆
      Set.Ioo (Real.exp (L - 2 * EvenKernel.δ C L))
        (Real.exp (L + 2 * EvenKernel.δ C L)) := by
  intro t ht
  have ht0 : 0 < t := by
    by_contra h
    exact ht (by simp [logWeight, h])
  have hk : smoothKernel j ((Real.log t - L) / EvenKernel.δ C L) ≠ 0 := by
    intro hk
    exact ht (by simp [logWeight, ht0, hk])
  have hs := smoothKernel_support j hk
  have hlo := (lt_div_iff₀ hδ).mp hs.1
  have hhi := (div_lt_iff₀ hδ).mp hs.2
  constructor
  · calc _ < Real.exp (Real.log t) := Real.exp_lt_exp.mpr (by linarith)
         _ = t := Real.exp_log ht0
  · calc t = Real.exp (Real.log t) := (Real.exp_log ht0).symm
         _ < _ := Real.exp_lt_exp.mpr (by linarith)

theorem logWeight_compact (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) :
    HasCompactSupport (logWeight j C L) := by
  apply exists_compact_iff_hasCompactSupport.mp
  refine ⟨Set.Icc (Real.exp (L - 2 * EvenKernel.δ C L))
    (Real.exp (L + 2 * EvenKernel.δ C L)), isCompact_Icc, ?_⟩
  intro t ht
  by_contra h
  exact ht (Set.Ioo_subset_Icc_self (logWeight_support j hδ h))

theorem logWeight_contDiff (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) :
    ContDiff ℝ ∞ (logWeight j C L) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · have hl : ContDiffAt ℝ ∞ Real.log t := Real.contDiffAt_log.mpr ht.ne'
    have hs : ContDiffAt ℝ ∞ (fun u : ℝ => (Real.log u - L) / EvenKernel.δ C L) t :=
      (hl.sub contDiffAt_const).div_const _
    have hk := (smoothKernel_contDiff j).contDiffAt.comp t hs
    have hr := hk.div (Real.contDiffAt_sqrt ht.ne') (Real.sqrt_pos.mpr ht).ne'
    apply hr.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact if_pos hu
  · have ha : t < Real.exp (L - 2 * EvenKernel.δ C L) :=
      (le_of_not_gt ht).trans_lt (Real.exp_pos _)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ha] with u hu
    by_contra h
    have hs := logWeight_support j hδ h
    have hh : u < Real.exp (L - 2 * EvenKernel.δ C L) := hu
    linarith [hs.1]

noncomputable def greenWeight (j : ℕ) (C L t : ℝ) : ℝ := logWeight j C L (2 * t)

theorem greenWeight_contDiff (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) :
    ContDiff ℝ ∞ (greenWeight j C L) :=
  (logWeight_contDiff j hδ).comp (contDiff_const.mul contDiff_id)

theorem greenWeight_compact (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) :
    HasCompactSupport (greenWeight j C L) := by
  apply exists_compact_iff_hasCompactSupport.mp
  refine ⟨Set.Icc (Real.exp (L - 2 * EvenKernel.δ C L) / 2)
    (Real.exp (L + 2 * EvenKernel.δ C L) / 2), isCompact_Icc, ?_⟩
  intro t ht
  by_contra h
  have hs := logWeight_support j hδ h
  exact ht ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- All hypotheses concerning W of Green's Theorem7.1 are discharged for this
actual W and X=2. The independently published theorem itself is not an axiom here. -/
theorem greenWeight_admissible (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L)
    (ha : 2 ≤ Real.exp (L - 2 * EvenKernel.δ C L)) :
    ContDiff ℝ ∞ (greenWeight j C L) ∧ HasCompactSupport (greenWeight j C L) ∧
      Function.support (greenWeight j C L) ⊆ Set.Ici 1 ∧ (1 : ℝ) < 2 := by
  refine ⟨greenWeight_contDiff j hδ, greenWeight_compact j hδ, ?_, by norm_num⟩
  intro t ht
  have hs := logWeight_support j hδ ht
  change 1 ≤ t
  linarith [hs.1]

theorem greenWeight_admissible_on_full_ray (j : ℕ) {C L : ℝ}
    (hC : C ∈ Set.Icc (103 / 100 : ℝ) 16) (hL : 24 ≤ L) :
    ContDiff ℝ ∞ (greenWeight j C L) ∧ HasCompactSupport (greenWeight j C L) ∧
      Function.support (greenWeight j C L) ⊆ Set.Ici 1 ∧ (1 : ℝ) < 2 := by
  have hd : 0 < EvenKernel.D C L := by unfold EvenKernel.D; nlinarith [hC.1]
  have hδ : 0 < EvenKernel.δ C L := mul_pos hd (Real.exp_pos _)
  apply greenWeight_admissible j hδ
  have hs := RHLimit.OcticGeometry.delta_small hC hL
  calc
    (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    _ ≤ Real.exp (L - 2 * EvenKernel.δ C L) := Real.exp_le_exp.mpr (by linarith)

/-- Exact source-to-application prime-power observable, including n=0 and the
finite support cap. The factor n^-1/2 is not lost in the normalization. -/
theorem green_mangoldt_sum (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) :
    (∑' k : ℕ, (ArithmeticFunction.vonMangoldt k : ℝ) *
      greenWeight j C L ((k : ℝ) / 2)) = smoothPopulation j C L := by
  rw [smoothPopulation_eq_tsum j hδ]
  apply tsum_congr
  intro k
  by_cases hk0 : k = 0
  · simp [hk0]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  unfold greenWeight logWeight
  rw [show 2 * ((k : ℝ) / 2) = k by ring, if_pos hkpos]
  ring

#print axioms logWeight_contDiff
#print axioms greenWeight_admissible
#print axioms greenWeight_admissible_on_full_ray
#print axioms green_mangoldt_sum
end RHOcticPush.PhysicalWeight
