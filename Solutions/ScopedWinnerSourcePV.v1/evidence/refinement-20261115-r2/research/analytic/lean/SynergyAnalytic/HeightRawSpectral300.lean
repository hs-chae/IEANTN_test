/- Actual zero-sum budget on the entire300ray, using the genuine earlier source
count-at-truncation proof rather than a parameter substitution. -/
import SynergyAnalytic.HeightBudget300
import SynergyAnalytic.CountCellOrdinate100
namespace SynergyAnalytic
open Real Set IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
open WinnerDensityA CH2QRH
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem height_raw_spectral_300 {a c D : Nat → ℝ} {n : Nat}
    (monotone : Monotone a) (first : a 0=WinnerOriginalScalars.height)
    (last : a n=Real.exp 60)
    (weights : ∀ i < n, 0 ≤ (1/a i-1/a (i+1))*c i)
    (slopes : ∀ i < n, 0 ≤ D i ∧ D i ≤ 163)
    (checked : 2*(∑ i ∈ Finset.range n,
      ((1/a i-1/a (i+1))*c i)*pairedFactor (D i) (1/8) 330) ≤
        8433850764/1000000000000)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (caps : ActualHeightCaps a c D n)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {L : ℝ} (future : 300 ≤ L) :
    rawSpectral (Real.exp (L/3)) (Real.exp L)*Real.exp (L/8) ≤
      935466375/100000000000 := by
  have thousand : (1000:ℝ) ≤ Real.exp (L/3) := by
    calc
      (1000:ℝ) ≤ 2^100 := by norm_num
      _ ≤ (Real.exp 1)^100 := pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.add_one_le_exp (1:ℝ)]) 100
      _ = Real.exp 100 := by rw [←Real.exp_nat_mul];norm_num
      _ ≤ Real.exp (L/3) := Real.exp_le_exp.mpr (by linarith)
  have truncation : Real.exp 100 ≤ Real.exp (L/3) := Real.exp_le_exp.mpr (by linarith)
  have spectral := actual_spectral_from_continuous_envelope hrvm hsmall hlow thousand
    (Real.exp_pos L) (by norm_num : (0:ℝ)≤300)
    (by simpa only [Real.log_exp] using future) hQRH
    (ordinateProfile a c D n) (ordinateProfile_continuous a c D n)
    (fun s hs=>source_ordinate_from_count_cells_at100 monotone first last h caps hRH
      hs.1 hs.2 truncation)
  have base := density_count_base_row (L₀:=300) (L:=L) (τ:=100) (t:=Real.exp (L/3))
    (by norm_num) future (by norm_num) (by linarith)
    (by rw [Real.log_exp];norm_num;linarith)
  have power : (Real.exp L)^((1:ℝ)/8)=Real.exp (L/8) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp]
    congr 1
    ring
  rw [power,Real.log_exp,ordinate_paired_coefficient] at spectral
  exact (spectral.trans (add_le_add base le_rfl)).trans
    (height_spectral_budget_300 weights slopes checked)

#print axioms height_raw_spectral_300
end SynergyAnalytic
