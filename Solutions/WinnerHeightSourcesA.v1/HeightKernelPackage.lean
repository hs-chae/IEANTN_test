/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import Height0Integral
import Height1Integral
import Height2Integral
import Height3Integral
import HeightProfileScalars
import WinnerBetaA.SignedHeight
namespace WinnerHeightProfiles
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def profileKernel (j : Fin 4) : ℝ→ℝ :=
  WinnerBetaA.SignedHeight.kernel (row j).m1 (row j).m2 (row j).h (row j).r0 (row j).r1

def Jcap (j : Fin 4) : ℚ := match j.val with
  | 0 => 3550829/1000000
  | 1 => 882173/250000
  | 2 => 877061/250000
  | _ => 3471693/1000000

theorem kernel_zero : profileKernel 0=WinnerHeightKernel0.kernelAll := by
  funext y
  norm_num [profileKernel,WinnerBetaA.SignedHeight.kernel,row,WinnerHeightKernel0.kernelAll]
theorem kernel_one : profileKernel 1=WinnerHeightKernel1.kernelAll := by
  funext y
  norm_num [profileKernel,WinnerBetaA.SignedHeight.kernel,row,WinnerHeightKernel1.kernelAll]
theorem kernel_two : profileKernel 2=WinnerHeightKernel2.kernelAll := by
  funext y
  norm_num [profileKernel,WinnerBetaA.SignedHeight.kernel,row,WinnerHeightKernel2.kernelAll]
theorem kernel_three : profileKernel 3=WinnerHeightKernel3.kernelAll := by
  funext y
  norm_num [profileKernel,WinnerBetaA.SignedHeight.kernel,row,WinnerHeightKernel3.kernelAll]

theorem profile_integrable (j : Fin 4) : Integrable (profileKernel j) := by
  fin_cases j
  · change Integrable (profileKernel (0:Fin 4))
    rw [kernel_zero];exact WinnerHeightKernel0.kernel_integrable
  · change Integrable (profileKernel (1:Fin 4))
    rw [kernel_one];exact WinnerHeightKernel1.kernel_integrable
  · change Integrable (profileKernel (2:Fin 4))
    rw [kernel_two];exact WinnerHeightKernel2.kernel_integrable
  · change Integrable (profileKernel (3:Fin 4))
    rw [kernel_three];exact WinnerHeightKernel3.kernel_integrable

theorem profile_J_upper (j : Fin 4) : (∫ y : ℝ,profileKernel j y)≤Jcap j := by
  fin_cases j
  · change (∫ y : ℝ,profileKernel (0:Fin 4) y) ≤ (Jcap (0:Fin 4):ℝ)
    rw [kernel_zero];convert WinnerHeightKernel0.full_integral_bound using 1 <;> norm_num [Jcap]
  · change (∫ y : ℝ,profileKernel (1:Fin 4) y) ≤ (Jcap (1:Fin 4):ℝ)
    rw [kernel_one];convert WinnerHeightKernel1.full_integral_bound using 1 <;> norm_num [Jcap]
  · change (∫ y : ℝ,profileKernel (2:Fin 4) y) ≤ (Jcap (2:Fin 4):ℝ)
    rw [kernel_two];convert WinnerHeightKernel2.full_integral_bound using 1 <;> norm_num [Jcap]
  · change (∫ y : ℝ,profileKernel (3:Fin 4) y) ≤ (Jcap (3:Fin 4):ℝ)
    rw [kernel_three];convert WinnerHeightKernel3.full_integral_bound using 1 <;> norm_num [Jcap]

theorem profile_finite_U (j : Fin 4) :
    8*(601/5000:ℝ)*(1000000000001/1000000000000)*(611/1000)^2*Jcap j≤(row j).U := by
  fin_cases j <;> norm_num [Jcap,row]

#print axioms profile_integrable
#print axioms profile_J_upper
#print axioms profile_finite_U
end WinnerHeightProfiles
