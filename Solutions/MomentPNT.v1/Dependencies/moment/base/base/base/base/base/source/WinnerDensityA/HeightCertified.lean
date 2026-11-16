/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.HeightContext
import HeightKernelPackage
namespace WinnerNewHeightSource
open Real Set MeasureTheory
open WinnerOriginalScalars WinnerHeightProfiles WinnerDensitySource
set_option maxHeartbeats 0

/-- All fields are supplied by executed exact scalar/kernel providers and
proved denotation/tail/convergence theorems. No moment bound is a field. -/
noncomputable def profileCertificate (j:Fin 4) :
    KernelCertificate (anchor j) (row j).U where
  M1 := (row j).m1
  M2 := (row j).m2
  hbar := (row j).h
  r0 := (row j).r0
  r1 := (row j).r1
  J := Jcap j
  omegaBar := 1000000000001/1000000000000
  mean_one := mean_one_upper j
  mean_two := mean_two_upper j
  log_pos := by fin_cases j <;> norm_num [row]
  log_lower := log_lower j
  ratio_zero := ratio_zero_upper j
  ratio_one := ratio_one_upper j
  kernel_integrable := profile_integrable j
  kernel_budget := profile_J_upper j
  omega_upper := omega_upper j
  finite_U := profile_finite_U j

/-- Four actual height providers, under the one common parameterized source
package. Every new operand and numerical enclosure is consumed concretely.
Finite RH is still required only through the original height H=3e12. -/
theorem profile_count (h:NewInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo height) (j:Fin 4)
    {sigma T:ℝ} (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8) (hT:anchor j≤T) :
    IEANTN.zetaN' sigma T≤((row j).K:ℝ)*exp (-(54281/10000:ℝ)*(7/8-sigma))*
      T^(8*(1-sigma)/3)*log T^(5-2*sigma)+6*log T^(2:ℕ) := by
  apply count_at_anchor h (by norm_num) (by norm_num) (by norm_num)
    (height_le_anchor j) hT (row_U_pos j) (row_V_pos j) (profileCertificate j)
    (right_v_upper j) ?_ ?_ hRH hs hs'
  · simpa only [alpha] using coefficient_upper j
  · simpa only [densitySlope] using slope_lower j

#print axioms profile_count
#check profile_count
end WinnerNewHeightSource
