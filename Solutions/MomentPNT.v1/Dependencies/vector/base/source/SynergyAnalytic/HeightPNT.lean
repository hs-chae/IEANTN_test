import SynergyAnalytic.ProfileCoefficient
import SynergyAnalytic.PNTTransfer
namespace SynergyAnalytic
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option maxHeartbeats 0

noncomputable def finalCoefficient (a c D:ℕ→ℝ) (n:ℕ) : ℝ :=
  (1+1/1000000000)*(spectralBase 330 110+profileCoefficient a c D n 330)+
    1/1000000000000+1/100000000

/-- Complete original-source→PNT transfer for the new continuous-height
construction. The only new numerical obligations are three universal basis
caps and the full-cell output contract; the explicit final coefficient is a
finite formula. No new density/moment/interpolation assumption is introduced. -/
theorem source_pi_from_height_cells {a c D:ℕ→ℝ} {n:ℕ}
    (ha:Monotone a) (ha0:a 0=WinnerOriginalScalars.height) (han:a n=Real.exp 60)
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hcaps:UniversalBasisCaps (373/200) (1273/2000) (129/250))
    (hcells:HeightCellCaps a c D n)
    (hCHJ:OriginalCHJSource) (hrvm:ZeroCount.v1.rvm_error_bound)
    (hsmall:ZeroCount.v1.rvm_error_small) (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (finalCoefficient a c D n) 0 (7/8) (Real.exp 330) := by
  have hh := pi_from_continuous_ordinate_envelope hCHJ hrvm hsmall hlow hRH hQRH
    (L0:=330) (C:=spectralBase 330 110+profileCoefficient a c D n 330)
    (by norm_num) (ordinateProfile a c D n) (ordinateProfile_continuous a c D n)
    (fun {s t} hs ht=>source_ordinate_profile ha ha0 han h hcaps hcells hRH hs.1 hs.2
      (by simpa only [show (330:ℝ)/3=110 by norm_num] using ht))
    (by rw [ordinate_paired_coefficient];norm_num)
  exact hh

/-- Acceptance wrapper for the preselected0.00845 target. This is explicitly
conditional on the displayed numerical residuals; until the source program
proves them, it is not an accepted numerical instance. -/
theorem source_pi_00845_of_budget {a c D:ℕ→ℝ} {n:ℕ}
    (ha:Monotone a) (ha0:a 0=WinnerOriginalScalars.height) (han:a n=Real.exp 60)
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hcaps:UniversalBasisCaps (373/200) (1273/2000) (129/250))
    (hcells:HeightCellCaps a c D n) (hbudget:finalCoefficient a c D n ≤ 169/20000)
    (hCHJ:OriginalCHJSource) (hrvm:ZeroCount.v1.rvm_error_bound)
    (hsmall:ZeroCount.v1.rvm_error_small) (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (169/20000) 0 (7/8) (Real.exp 330) := by
  have hb := source_pi_from_height_cells ha ha0 han h hcaps hcells hCHJ hrvm hsmall hlow hRH hQRH
  intro x hx
  have hh := hb x hx
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  simp only [pow_zero,mul_one] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_right hbudget (by positivity))

#print axioms source_pi_from_height_cells
#print axioms source_pi_00845_of_budget
end SynergyAnalytic
