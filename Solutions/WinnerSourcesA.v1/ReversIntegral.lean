/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ReversKernel
import ReversTails
namespace WinnerReversDensity
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def kernelAll (y : ℝ) : ℝ :=
  exp (2*y-(601/2500)*exp (2*y)) *
    (sqrt ((129/200)*exp y+23/250) *
      (exp (y/6)*(1+|y|/28)+137/100000) +
      (47/500000)*exp (y/2))^2

theorem kernelAll_nonneg (y : ℝ) : 0 ≤ kernelAll y := by unfold kernelAll; positivity
theorem kernelAll_continuous : Continuous kernelAll := by unfold kernelAll; fun_prop
theorem kernelAll_neg {y : ℝ} (hy : y ≤ 0) : kernelAll y=kernelReal (-1) y := by
  simp [kernelAll,kernelReal,abs_of_nonpos hy]
theorem kernelAll_pos {y : ℝ} (hy : 0 ≤ y) : kernelAll y=kernelReal 1 y := by
  simp [kernelAll,kernelReal,abs_of_nonneg hy]

theorem low_all_pointwise (y : ℝ) (hy : y ≤ -20) : kernelAll y ≤ 4*exp y := by
  rw [kernelAll_neg (by linarith : y≤0)]
  exact low_pointwise y hy

theorem high_all_pointwise (y : ℝ) (hy : 3 ≤ y) : kernelAll y ≤ 9*exp (-y-20) := by
  rw [kernelAll_pos (by linarith : 0≤y)]
  exact high_pointwise y hy

theorem low_integrable : IntegrableOn kernelAll (Iic (-20)) := by
  have hi := (integrableOn_exp_Iic (-20)).const_mul (4:ℝ)
  apply hi.mono' kernelAll_continuous.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg (kernelAll_nonneg y)]
  exact low_all_pointwise y hy

theorem high_integrable : IntegrableOn kernelAll (Ioi 3) := by
  have hi := (integrableOn_exp_neg_Ioi 3).const_mul ((9:ℝ)*exp (-20))
  apply hi.mono' kernelAll_continuous.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg (kernelAll_nonneg y)]
  have hp := high_all_pointwise y hy.le
  convert hp using 1
  rw [show -y-20=(-20)+(-y) by ring,exp_add]
  ring

theorem kernel_integrable : Integrable kernelAll := by
  have hm : IntegrableOn kernelAll (Ioc (-20) 3) :=
    (kernelAll_continuous.intervalIntegrable (-20) 3).1
  have hu := low_integrable.union hm
  have he : Iic (-20:ℝ) ∪ Ioc (-20) 3=Iic 3 := by
    ext x
    simp only [mem_union,mem_Iic,mem_Ioc]
    constructor
    · rintro (h|⟨h1,h2⟩) <;> linarith
    · intro h
      by_cases hlow : x≤-20
      · exact Or.inl hlow
      · exact Or.inr ⟨by linarith,h⟩
  rw [he] at hu
  have hall := hu.union high_integrable
  rw [Iic_union_Ioi,integrableOn_univ] at hall
  exact hall

theorem exp_twenty_tail : (9:ℝ)*exp (-20) ≤ 1/100000 := by
  have hp : (2:ℝ)^20 ≤ exp 20 := by
    calc
      _ ≤ (exp 1)^20 := by gcongr; exact exp_one_gt_two.le
      _ = _ := by simpa using (exp_nat_mul (1:ℝ) 20).symm
  have hi := one_div_le_one_div_of_le (by positivity : (0:ℝ)<2^20) hp
  rw [exp_neg]
  norm_num [one_div] at hi ⊢
  linarith

theorem low_tail_bound : (∫ y in Iic (-20:ℝ), kernelAll y) ≤ 1/100000 := by
  have h := setIntegral_mono_on low_integrable
    ((integrableOn_exp_Iic (-20)).const_mul (4:ℝ)) measurableSet_Iic
    (fun y hy => low_all_pointwise y hy)
  rw [integral_const_mul,integral_exp_Iic] at h
  have he := exp_twenty_tail
  nlinarith [exp_pos (-20)]

theorem high_tail_bound : (∫ y in Ioi (3:ℝ), kernelAll y) ≤ 1/100000 := by
  have heq : (fun y : ℝ => 9*exp (-y-20)) = fun y => (9*exp (-20))*exp (-y) := by
    funext y
    rw [show -y-20=(-20)+(-y) by ring,exp_add]
    ring
  have hi : IntegrableOn (fun y : ℝ => 9*exp (-y-20)) (Ioi 3) := by
    rw [heq]
    exact (integrableOn_exp_neg_Ioi 3).const_mul _
  have h := setIntegral_mono_on high_integrable hi measurableSet_Ioi
    (fun y hy => high_all_pointwise y hy.le)
  rw [heq,integral_const_mul,integral_exp_neg_Ioi] at h
  have hx : exp (-3) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
  nlinarith [exp_twenty_tail,exp_pos (-20)]

theorem full_integral_bound : (∫ y : ℝ, kernelAll y) ≤ (358075/100000:ℝ) := by
  have hn : (∫ y in (-20:ℝ)..0,kernelAll y) ≤ 21073/100000 := by
    convert negative_integral using 1
    apply intervalIntegral.integral_congr
    intro y hy
    exact kernelAll_neg (by simpa using hy.2)
  have hp : (∫ y in (0:ℝ)..3,kernelAll y) ≤ 337/100 := by
    convert positive_integral using 1
    apply intervalIntegral.integral_congr
    intro y hy
    exact kernelAll_pos (by simpa using hy.1)
  have h0 := intervalIntegral.integral_Iic_sub_Iic
    (kernel_integrable.integrableOn (s:=Iic (-20)))
    (kernel_integrable.integrableOn (s:=Iic 0))
  have h3 := intervalIntegral.integral_Iic_sub_Iic
    (kernel_integrable.integrableOn (s:=Iic 0))
    (kernel_integrable.integrableOn (s:=Iic 3))
  have ha := intervalIntegral.integral_Iic_add_Ioi
    (kernel_integrable.integrableOn (s:=Iic 3))
    (kernel_integrable.integrableOn (s:=Ioi 3))
  linarith [low_tail_bound,high_tail_bound]

#print axioms kernel_integrable
#print axioms full_integral_bound
end WinnerReversDensity
