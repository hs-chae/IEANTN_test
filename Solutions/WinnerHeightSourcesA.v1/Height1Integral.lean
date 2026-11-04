/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICEWinnerHeightKernel1E.
Authors: OpenAI (Codex)
-/
import Height1Kernel
import OriginalIntegral
namespace WinnerHeightKernel1
open Real Set MeasureTheory
set_option maxHeartbeats 0
noncomputable def kernelAll (y : ℝ) : ℝ :=
  exp (2*y-(601/2500)*exp (2*y)) *
    (sqrt ((643179/1000000)*exp y+(43091/500000)) *
      (exp (y/6)*(1+max y 0/(29729633/1000000))+(109037/100000000)) + (7117/100000000)*exp (y/2))^2

theorem kernelAll_nonneg (y : ℝ) : 0 ≤ kernelAll y := by unfold kernelAll; positivity
theorem kernelAll_continuous : Continuous kernelAll := by unfold kernelAll;fun_prop

theorem kernelAll_neg {y : ℝ} (hy : y ≤ 0) : kernelAll y=kernelReal 0 y := by
  simp [kernelAll,kernelReal,max_eq_right hy]
theorem kernelAll_pos {y : ℝ} (hy : 0 ≤ y) : kernelAll y=kernelReal 1 y := by
  simp [kernelAll,kernelReal,max_eq_left hy]

theorem dominated_by_original (y : ℝ) : kernelAll y ≤ WinnerOriginalDensity.kernelAll y := by
  have hm : max y 0 ≤ |y| := max_le (le_abs_self y) (abs_nonneg y)
  have hdiv : max y 0/(29729633/1000000) ≤ |y|/28 := by
    calc
      _ ≤ |y|/(29729633/1000000) := div_le_div_of_nonneg_right hm (by norm_num)
      _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg y) (by norm_num) (by norm_num)
  have hf : 1+max y 0/(29729633/1000000) ≤ 1+|y|/28 := by linarith
  have hmax : 0 ≤ max y 0 := le_max_right y 0
  unfold kernelAll WinnerOriginalDensity.kernelAll
  gcongr (exp (2*y-(601/2500)*exp (2*y)) *
    (sqrt (?_ * exp y + ?_) * (exp (y/6) * ?_ + ?_) + ?_ * exp (y/2))^2) <;>
    first | exact hf | norm_num

theorem kernel_integrable : Integrable kernelAll := by
  apply WinnerOriginalDensity.kernel_integrable.mono' kernelAll_continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs,abs_of_nonneg (kernelAll_nonneg y)]
    exact dominated_by_original y

theorem low_tail_bound : (∫ y in Iic (-20:ℝ),kernelAll y) ≤ 1/100000 := by
  exact (setIntegral_mono_on (kernel_integrable.integrableOn (s:=Iic (-20)))
    WinnerOriginalDensity.low_integrable measurableSet_Iic
    (fun y _ => dominated_by_original y)).trans WinnerOriginalDensity.low_tail_bound

theorem high_tail_bound : (∫ y in Ioi (3:ℝ),kernelAll y) ≤ 1/100000 := by
  exact (setIntegral_mono_on (kernel_integrable.integrableOn (s:=Ioi 3))
    WinnerOriginalDensity.high_integrable measurableSet_Ioi
    (fun y _ => dominated_by_original y)).trans WinnerOriginalDensity.high_tail_bound

theorem full_integral_bound : (∫ y : ℝ,kernelAll y) ≤ 882173/250000 := by
  have hn : (∫ y in (-20:ℝ)..0,kernelAll y) ≤ 100103/500000 := by
    convert negative_integral using 1
    apply intervalIntegral.integral_congr
    intro y hy
    exact kernelAll_neg (by simpa using hy.2)
  have hp : (∫ y in (0:ℝ)..3,kernelAll y) ≤ 1664233/500000 := by
    convert positive_integral using 1
    apply intervalIntegral.integral_congr
    intro y hy
    exact kernelAll_pos (by simpa using hy.1)
  have h0 := intervalIntegral.integral_Iic_sub_Iic
    (kernel_integrable.integrableOn (s:=Iic (-20))) (kernel_integrable.integrableOn (s:=Iic 0))
  have h3 := intervalIntegral.integral_Iic_sub_Iic
    (kernel_integrable.integrableOn (s:=Iic 0)) (kernel_integrable.integrableOn (s:=Iic 3))
  have ha := intervalIntegral.integral_Iic_add_Ioi
    (kernel_integrable.integrableOn (s:=Iic 3)) (kernel_integrable.integrableOn (s:=Ioi 3))
  linarith [low_tail_bound,high_tail_bound]

theorem finite_U : 8*(601/5000:ℝ)*(1000000000001/1000000000000)*(611/1000)^2*(882173/250000) ≤ 3167/2500 := by norm_num
#print axioms kernel_integrable
#print axioms full_integral_bound
#print axioms finite_U
end WinnerHeightKernel1
