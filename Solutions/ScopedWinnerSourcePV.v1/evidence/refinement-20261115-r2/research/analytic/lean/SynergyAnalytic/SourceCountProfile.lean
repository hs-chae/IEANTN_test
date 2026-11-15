/- Actual whole-cell count caps supply the entire log-x ray profile. -/
import SynergyAnalytic.HeightProfile
import SynergyAnalytic.CountCellOrdinate
namespace SynergyAnalytic
open Real Set MeasureTheory IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel WinnerDensityA CH2QRH
set_option maxHeartbeats 0

/-- One certified height vector supplies a whole family of ray coefficients,
not only the single330 endpoint. This is the exact formula queried by the
actual source-count family at every L0≥330. -/
theorem source_pi_count_profile_ray {a c D:ℕ→ℝ} {n:ℕ} {L0:ℝ}
    (ha:Monotone a) (ha0:a 0=WinnerOriginalScalars.height) (han:a n=Real.exp 60)
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hcells:ActualHeightCaps a c D n)
    (hCHJ:OriginalCHJSource) (hrvm:ZeroCount.v1.rvm_error_bound)
    (hsmall:ZeroCount.v1.rvm_error_small) (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height) (hQRH:ZetaZeroFreeHalfPlane (7/8))
    (h330:330 ≤ L0) :
    HasPowerLogBound Eπ (rayCoefficient a c D n L0) 0 (7/8) (Real.exp L0) := by
  apply rh_pi_ray_of_budgets hCHJ hQRH hlow (by linarith : 300 ≤ L0)
  · intro L hL
    have hL330 : 330 ≤ L := h330.trans hL
    have h1000 : (1000:ℝ) ≤ Real.exp (L/3) := by
      calc
        (1000:ℝ) ≤ 2^100 := by norm_num
        _ ≤ (Real.exp 1)^100 := pow_le_pow_left₀ (by norm_num)
          (by linarith [Real.add_one_le_exp (1:ℝ)]) 100
        _ = Real.exp 100 := by rw [←Real.exp_nat_mul];norm_num
        _ ≤ Real.exp (L/3) := Real.exp_le_exp.mpr (by linarith)
    have ht : Real.exp 110 ≤ Real.exp (L/3) := Real.exp_le_exp.mpr (by linarith)
    have hs := actual_spectral_from_continuous_envelope hrvm hsmall hlow h1000
      (Real.exp_pos L) (by linarith : 0 ≤ L0) (by simpa only [Real.log_exp] using hL)
      hQRH (ordinateProfile a c D n) (ordinateProfile_continuous a c D n)
      (fun s hs=>source_ordinate_from_count_cells ha ha0 han h hcells hRH hs.1 hs.2 ht)
    have hbase := density_count_base_row (L₀:=330) (L:=L) (τ:=110) (t:=Real.exp (L/3))
      (by norm_num) hL330 (by norm_num) (by linarith) (by rw [Real.log_exp];norm_num;linarith)
    have hexp : (Real.exp L)^((1:ℝ)/8)=Real.exp (L/8) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp]
      congr 1
      ring
    rw [hexp,Real.log_exp,ordinate_paired_coefficient] at hs
    exact hs.trans (add_le_add hbase le_rfl)
  · intro L hL
    exact low_paired_kernel_tiny hQRH hRH hrvm hsmall hlow (by linarith)

/-- Equivalent pointwise full-function form, with the same numerical vector
and the original source assumptions. -/
theorem source_pi_count_profile_point {a c D:ℕ→ℝ} {n:ℕ} {x:ℝ}
    (ha:Monotone a) (ha0:a 0=WinnerOriginalScalars.height) (han:a n=Real.exp 60)
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hcells:ActualHeightCaps a c D n)
    (hCHJ:OriginalCHJSource) (hrvm:ZeroCount.v1.rvm_error_bound)
    (hsmall:ZeroCount.v1.rvm_error_small) (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height) (hQRH:ZetaZeroFreeHalfPlane (7/8))
    (hx:Real.exp 330 ≤ x) : Eπ x ≤ rayCoefficient a c D n (Real.log x)*x^(-(1:ℝ)/8) := by
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  have hl : 330 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos 330) hx
    simpa only [Real.log_exp] using hh
  have hb := source_pi_count_profile_ray ha ha0 han h hcells hCHJ hrvm hsmall hlow hRH hQRH hl
  have hh := hb x (by rw [Real.exp_log hx0])
  simpa only [pow_zero,mul_one,show (7/8:ℝ)-1= -1/8 by norm_num] using hh

#print axioms source_pi_count_profile_ray
#print axioms source_pi_count_profile_point
end SynergyAnalytic
