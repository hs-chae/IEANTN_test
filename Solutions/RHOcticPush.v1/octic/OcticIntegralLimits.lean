import OcticPhysicalWeight

/-! Actual physical-domain main/trivial limits in the mollifier route. Compact
support and positivity keep every logarithm and denominator on its source domain. -/
namespace RHOcticPush.IntegralLimits
open Real Set Filter MeasureTheory
open scoped Topology
open RHOcticPush.Mollifier RHOcticPush.FourierMollifier RHOcticPush.PhysicalWeight
set_option maxHeartbeats 0

noncomputable def physicalTest (C L : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 < t then EvenKernel.kernel 4 ((Real.log t - L) / EvenKernel.δ C L) * g t else 0

lemma physicalTest_support {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) (g : ℝ → ℝ) :
    Function.support (physicalTest C L g) ⊆ Set.Ioo (EvenKernel.a C L) (EvenKernel.b C L) := by
  intro t ht
  have ht0 : 0 < t := by
    by_contra h
    exact ht (by simp [physicalTest, h])
  have hk : EvenKernel.kernel 4 ((Real.log t - L) / EvenKernel.δ C L) ≠ 0 := by
    intro hk
    exact ht (by simp [physicalTest, ht0, hk])
  have hs := kernel_support hk
  have hlo := (lt_div_iff₀ hδ).mp hs.1
  have hhi := (div_lt_iff₀ hδ).mp hs.2
  constructor
  · calc EvenKernel.a C L < Real.exp (Real.log t) := Real.exp_lt_exp.mpr (by linarith)
         _ = t := Real.exp_log ht0
  · calc t = Real.exp (Real.log t) := (Real.exp_log ht0).symm
         _ < EvenKernel.b C L := Real.exp_lt_exp.mpr (by linarith)

theorem extend_original_integral {C L A B : ℝ} (hδ : 0 < EvenKernel.δ C L)
    (hA0 : 0 < A) (hAa : A ≤ EvenKernel.a C L) (hbB : EvenKernel.b C L ≤ B)
    (g : ℝ → ℝ) :
    (∫ t in A..B, EvenKernel.kernel 4 ((Real.log t - L) / EvenKernel.δ C L) * g t) =
      ∫ t in EvenKernel.a C L..EvenKernel.b C L,
        EvenKernel.kernel 4 ((Real.log t - L) / EvenKernel.δ C L) * g t := by
  have hab : EvenKernel.a C L ≤ EvenKernel.b C L :=
    Real.exp_le_exp.mpr (by linarith)
  have hAB : A ≤ B := hAa.trans (hab.trans hbB)
  have hs := physicalTest_support hδ g
  have hsmall := intervalIntegral.integral_eq_integral_of_support_subset
    (μ := volume)
    (show Function.support (physicalTest C L g) ⊆
      Set.Ioc (EvenKernel.a C L) (EvenKernel.b C L) from
      fun t ht => Set.Ioo_subset_Ioc_self (hs ht))
  have hlarge := intervalIntegral.integral_eq_integral_of_support_subset
    (μ := volume)
    (show Function.support (physicalTest C L g) ⊆ Set.Ioc A B from
      fun t ht => ⟨hAa.trans_lt (hs ht).1, (hs ht).2.le.trans hbB⟩)
  have he1 : (∫ t in A..B, physicalTest C L g t) =
      ∫ t in A..B, EvenKernel.kernel 4 ((Real.log t - L) / EvenKernel.δ C L) * g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    exact if_pos (hA0.trans_le ht.1)
  have he2 : (∫ t in EvenKernel.a C L..EvenKernel.b C L, physicalTest C L g t) =
      ∫ t in EvenKernel.a C L..EvenKernel.b C L,
        EvenKernel.kernel 4 ((Real.log t - L) / EvenKernel.δ C L) * g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact if_pos ((Real.exp_pos _).trans_le ht.1)
  exact he1.symm.trans (hlarge.trans (hsmall.symm.trans he2))

theorem weighted_physical_limit {C L : ℝ} (hδ : 0 < EvenKernel.δ C L)
    {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.uIcc (Real.exp (L - 2 * EvenKernel.δ C L))
      (Real.exp (L + 2 * EvenKernel.δ C L)))) :
    Tendsto (fun j : ℕ => ∫ t in Real.exp (L - 2 * EvenKernel.δ C L)..
        Real.exp (L + 2 * EvenKernel.δ C L),
      smoothKernel j ((Real.log t - L) / EvenKernel.δ C L) * g t)
      atTop (𝓝 (∫ t in EvenKernel.a C L..EvenKernel.b C L,
        EvenKernel.kernel 4 ((Real.log t - L) / EvenKernel.δ C L) * g t)) := by
  have hAB : Real.exp (L - 2 * EvenKernel.δ C L) ≤
      Real.exp (L + 2 * EvenKernel.δ C L) := Real.exp_le_exp.mpr (by linarith)
  have hs : ContinuousOn (fun t : ℝ => (Real.log t - L) / EvenKernel.δ C L)
      (Set.uIcc (Real.exp (L - 2 * EvenKernel.δ C L))
        (Real.exp (L + 2 * EvenKernel.δ C L))) := by
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    have ht0 : 0 < t := (Real.exp_pos _).trans_le ht.1
    exact ((Real.continuousAt_log ht0.ne').sub continuousAt_const).div_const _ |>.continuousWithinAt
  have h := weighted_composed_interval_limit hs hg
  rw [extend_original_integral hδ (Real.exp_pos _)
    (Real.exp_le_exp.mpr (by linarith)) (Real.exp_le_exp.mpr (by linarith)) g] at h
  exact h

noncomputable def smoothTrivial (j : ℕ) (C L : ℝ) : ℝ :=
  ∫ t in Real.exp (L - 2 * EvenKernel.δ C L)..Real.exp (L + 2 * EvenKernel.δ C L),
    smoothKernel j ((Real.log t - L) / EvenKernel.δ C L) /
      (Real.sqrt t * t * (t ^ 2 - 1))

theorem smoothTrivial_tends {C L : ℝ} (hδ : 0 < EvenKernel.δ C L)
    (hgap : 0 < L - 2 * EvenKernel.δ C L) :
    Tendsto (fun j : ℕ => smoothTrivial j C L) atTop (𝓝 (EvenKernel.trivialCost 4 C L)) := by
  have hAB : Real.exp (L - 2 * EvenKernel.δ C L) ≤
      Real.exp (L + 2 * EvenKernel.δ C L) := Real.exp_le_exp.mpr (by linarith)
  have hg : ContinuousOn (fun t : ℝ => 1 / (Real.sqrt t * t * (t ^ 2 - 1)))
      (Set.uIcc (Real.exp (L - 2 * EvenKernel.δ C L))
        (Real.exp (L + 2 * EvenKernel.δ C L))) := by
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    have ht1 : 1 < t := (Real.one_lt_exp_iff.mpr hgap).trans_le ht.1
    have ht0 : 0 < t := by linarith
    have hsq : t ^ 2 - 1 ≠ 0 := by nlinarith
    have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    have hden : Real.sqrt t * t * (t ^ 2 - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hst ht0.ne') hsq
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := first | exact hden | exact ht0.ne' | exact hsq | exact hst)
  simpa only [smoothTrivial, EvenKernel.trivialCost, div_eq_mul_inv, one_mul] using
    weighted_physical_limit hδ hg

theorem source_pole_eq_physical_integral (j : ℕ) (C L : ℝ) :
    2 * (∫ t : ℝ, greenWeight j C L t) = ∫ t : ℝ, logWeight j C L t := by
  unfold greenWeight
  rw [Measure.integral_comp_mul_left]
  norm_num <;> ring

theorem delta_exp_half (C L : ℝ) :
    EvenKernel.δ C L * Real.exp (L / 2) = EvenKernel.D C L := by
  unfold EvenKernel.δ
  rw [mul_assoc, ← Real.exp_add]
  rw [show -L / 2 + L / 2 = 0 by ring, Real.exp_zero, mul_one]

theorem smoothKernel_even (j : ℕ) (u : ℝ) : smoothKernel j (-u) = smoothKernel j u := by
  unfold smoothKernel
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_neg_eq_self (fun t : ℝ =>
    (bump j).normed volume t * EvenKernel.kernel 4 (-u - t)) volume]
  simp_rw [(bump j).normed_neg,
    show ∀ t : ℝ, -u - -t = -(u - t) by intro t; ring, kernel_even]

theorem even_exp_integral_eq_cosh {f : ℝ → ℝ} (hf : Continuous f)
    (heven : ∀ u, f (-u) = f u) (R a : ℝ) :
    (∫ u in -R..R, f u * Real.exp (a * u)) =
      ∫ u in -R..R, f u * Real.cosh (a * u) := by
  have hp : IntervalIntegrable (fun u : ℝ => f u * Real.exp (a * u)) volume (-R) R :=
    (hf.mul (by fun_prop)).intervalIntegrable _ _
  have hm : IntervalIntegrable (fun u : ℝ => f u * Real.exp (-(a * u))) volume (-R) R :=
    (hf.mul (by fun_prop)).intervalIntegrable _ _
  have hneg : (∫ u in -R..R, f u * Real.exp (-(a * u))) =
      ∫ u in -R..R, f u * Real.exp (a * u) := by
    simpa only [heven, mul_neg, neg_neg] using
      (intervalIntegral.integral_comp_neg (f := fun u : ℝ => f u * Real.exp (a * u))
        (a := -R) (b := R))
  have he : (fun u : ℝ => f u * Real.cosh (a * u)) =
      fun u => (f u * Real.exp (a * u) + f u * Real.exp (-(a * u))) / 2 := by
    funext u
    rw [Real.cosh_eq]
    ring
  rw [he, intervalIntegral.integral_div, intervalIntegral.integral_add hp hm, hneg]
  ring

noncomputable def smoothMain (j : ℕ) (C L : ℝ) : ℝ :=
  EvenKernel.D C L * ∫ u in (-2 : ℝ)..2, smoothKernel j u *
    Real.cosh (EvenKernel.δ C L * u / 2)

theorem smoothMain_tends (C L : ℝ) :
    Tendsto (fun j : ℕ => smoothMain j C L) atTop (𝓝 (EvenKernel.mainTerm 4 C L)) := by
  let f : ℝ → ℝ := fun u => EvenKernel.kernel 4 u * Real.cosh (EvenKernel.δ C L * u / 2)
  have hs : Function.support f ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro u hu
    have hk : EvenKernel.kernel 4 u ≠ 0 := by
      intro hk
      exact hu (by simp [f, hk])
    exact kernel_support hk
  have hsmall := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume)
    (show Function.support f ⊆ Set.Ioc (-1 : ℝ) 1 from
      fun u hu => Set.Ioo_subset_Ioc_self (hs hu))
  have hlarge := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume)
    (show Function.support f ⊆ Set.Ioc (-2 : ℝ) 2 from
      fun u hu => ⟨by linarith [(hs hu).1], by linarith [(hs hu).2]⟩)
  have he : (∫ u in (-2 : ℝ)..2, f u) = ∫ u in (-1 : ℝ)..1, f u :=
    hlarge.trans hsmall.symm
  have h := (weighted_interval_limit (a := (-2 : ℝ)) (b := 2)
    (g := fun u => Real.cosh (EvenKernel.δ C L * u / 2)) (by fun_prop)).const_mul (EvenKernel.D C L)
  dsimp only [f] at he
  rw [he] at h
  simpa only [smoothMain, EvenKernel.mainTerm] using h

#print axioms extend_original_integral
#print axioms weighted_physical_limit
#print axioms smoothTrivial_tends
#print axioms source_pole_eq_physical_integral
#print axioms smoothKernel_even
#print axioms even_exp_integral_eq_cosh
#print axioms smoothMain_tends
end RHOcticPush.IntegralLimits
