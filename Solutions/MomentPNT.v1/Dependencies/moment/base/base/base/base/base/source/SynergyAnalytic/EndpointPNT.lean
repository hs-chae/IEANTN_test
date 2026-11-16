import SynergyAnalytic.ProfileCoefficient
import SynergyAnalytic.CountCellOrdinate
import SynergyAnalytic.HeightPNT
namespace SynergyAnalytic
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option maxHeartbeats 0


/-- Complete original-source→PNT transfer for the new continuous-height
construction. The only new numerical obligations are three universal basis
caps and the full-cell output contract; the explicit final coefficient is a
finite formula. No new density/moment/interpolation assumption is introduced. -/
theorem source_pi_from_count_cells {a c D:ℕ→ℝ} {n:ℕ}
    (ha:Monotone a) (ha0:a 0=WinnerOriginalScalars.height) (han:a n=Real.exp 60)
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hcells:ActualHeightCaps a c D n)
    (hCHJ:OriginalCHJSource) (hrvm:ZeroCount.v1.rvm_error_bound)
    (hsmall:ZeroCount.v1.rvm_error_small) (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (finalCoefficient a c D n) 0 (7/8) (Real.exp 330) := by
  have hh := pi_from_continuous_ordinate_envelope hCHJ hrvm hsmall hlow hRH hQRH
    (L0:=330) (C:=spectralBase 330 110+profileCoefficient a c D n 330)
    (by norm_num) (ordinateProfile a c D n) (ordinateProfile_continuous a c D n)
    (fun {s t} hs ht=>source_ordinate_from_count_cells ha ha0 han h hcells hRH hs.1 hs.2
      (by simpa only [show (330:ℝ)/3=110 by norm_num] using ht))
    (by rw [ordinate_paired_coefficient];norm_num)
  exact hh

/-- Acceptance wrapper for the preselected0.00845 target. This is explicitly
conditional on the displayed numerical residuals; until the source program
proves them, it is not an accepted numerical instance. -/
theorem source_pi_00845_from_count_cells {a c D:ℕ→ℝ} {n:ℕ}
    (ha:Monotone a) (ha0:a 0=WinnerOriginalScalars.height) (han:a n=Real.exp 60)
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hcells:ActualHeightCaps a c D n) (hbudget:finalCoefficient a c D n ≤ 169/20000)
    (hCHJ:OriginalCHJSource) (hrvm:ZeroCount.v1.rvm_error_bound)
    (hsmall:ZeroCount.v1.rvm_error_small) (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (169/20000) 0 (7/8) (Real.exp 330) := by
  have hb := source_pi_from_count_cells ha ha0 han h hcells hCHJ hrvm hsmall hlow hRH hQRH
  intro x hx
  have hh := hb x hx
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  simp only [pow_zero,mul_one] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_right hbudget (by positivity))

/-- Full original-source ANT consumer for endpoint-enclosed height cells.
The three J caps are discharged by the actual272-cell kernel proof; only the
explicit point numerical outputs and final finite budget remain to instantiate. -/
theorem source_pi_00845_from_endpoint_cells {a c D:ℕ→ℝ} {n:ℕ}
    (ha:Monotone a) (ha0:a 0=WinnerOriginalScalars.height) (han:a n=Real.exp 60)
    (hwidth:∀i<n,Real.log (a (i+1))-Real.log (a i) ≤ 1)
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hpoint:EndpointHeightCaps a c D n)
    (hbudget:finalCoefficient a (fun i=>c i+726) D n ≤ 169/20000)
    (hCHJ:OriginalCHJSource) (hrvm:ZeroCount.v1.rvm_error_bound)
    (hsmall:ZeroCount.v1.rvm_error_small) (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (169/20000) 0 (7/8) (Real.exp 330) := by
  exact source_pi_00845_from_count_cells ha ha0 han h
    (endpoint_actual_height_caps ha ha0 han hwidth h hpoint hRH)
    hbudget hCHJ hrvm hsmall hlow hRH hQRH

#print axioms source_pi_from_count_cells
#print axioms source_pi_00845_from_count_cells
#print axioms source_pi_00845_from_endpoint_cells
end SynergyAnalytic
