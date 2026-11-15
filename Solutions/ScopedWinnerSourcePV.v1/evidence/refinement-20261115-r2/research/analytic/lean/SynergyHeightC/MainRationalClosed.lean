/- Closed same-premise source-backed and strongest shared-math kernel-only PNT
profiles. All768 source-model slope checks are discharged, with no new premise. -/
import SynergyHeightC.MainRationalRead
import SynergyHeightC.MainModelOnlyProfile
import SourcePointSlopesV1.All
namespace SynergyHeightC.MainRationalClosed
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
open SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem actual_observed_read : evalExpr SynergyC.Header.layout FullMainPrefix.service 1
    (FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) (.var "total")=
    some (SynergyC.SourceIntervalMath.represented MainObservedOutput.total,
      FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) :=
  (MainTotalOutput.read_total FullMainPrefix.service (SourceMainBudgetV1.Data.total 768) 768).trans
    (congrArg (fun out : ProofBox=>some (SynergyC.SourceIntervalMath.represented out,
      FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768)) MainObservedOutput.total_exact)

theorem source_profile_point
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 330 ≤ x) :
    Eπ x ≤ rationalHeightCoefficient (8433850764/1000000000000) (Real.log x)*x^(-(1:ℝ)/8) :=
  MainRationalRead.pi_rational_point_from_actual_total_read actual_observed_read
    SourcePointSlopesV1.All.bounds h hCHJ hrvm hsmall hlow hRH hQRH hx

theorem kernel_only_profile_point
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 330 ≤ x) :
    Eπ x ≤ rationalHeightCoefficient (8433850764/1000000000000) (Real.log x)*x^(-(1:ℝ)/8) :=
  MainModelOnlyProfile.model_rational_point SourcePointSlopesV1.All.bounds
    h hCHJ hrvm hsmall hlow hRH hQRH hx

theorem source_profile_ray {L : ℝ} (future : 330 ≤ L)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (rationalHeightCoefficient (8433850764/1000000000000) L)
      0 (7/8) (Real.exp L) := by
  intro x hx
  have positive : 0 < x := (Real.exp_pos L).trans_le hx
  have initial : Real.exp 330 ≤ x := (Real.exp_le_exp.mpr future).trans hx
  have logx : L ≤ Real.log x := by
    have bound := Real.log_le_log (Real.exp_pos L) hx
    simpa only [Real.log_exp] using bound
  have source := source_profile_point h hCHJ hrvm hsmall hlow hRH hQRH initial
  have budget := rationalHeightCoefficient_antitone
    (by norm_num : (0:ℝ) ≤ 8433850764/1000000000000) future logx
  simp only [pow_zero,mul_one,show (7/8:ℝ)-1= -1/8 by norm_num]
  exact source.trans (mul_le_mul_of_nonneg_right budget (by positivity))

theorem source_profile_capped {L cap : ℝ} (future : 330 ≤ L)
    (checked : rationalHeightCoefficient (8433850764/1000000000000) L ≤ cap)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ cap 0 (7/8) (Real.exp L) := by
  have source := source_profile_ray future h hCHJ hrvm hsmall hlow hRH hQRH
  intro x hx
  have positive : 0 < x := (Real.exp_pos L).trans_le hx
  have bound := source x hx
  simp only [pow_zero,mul_one] at bound ⊢
  exact bound.trans (mul_le_mul_of_nonneg_right checked (by positivity))

theorem source_pi_500
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (7648883/1000000000) 0 (7/8) (Real.exp 500) :=
  source_profile_capped (by norm_num) rational_checkpoint_500.le h hCHJ hrvm hsmall hlow hRH hQRH

theorem source_pi_1000
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (7010158/1000000000) 0 (7/8) (Real.exp 1000) :=
  source_profile_capped (by norm_num) rational_checkpoint_1000.le h hCHJ hrvm hsmall hlow hRH hQRH

theorem source_pi_1000000
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (6470481/1000000000) 0 (7/8) (Real.exp 1000000) :=
  source_profile_capped (by norm_num) rational_checkpoint_1000000.le h hCHJ hrvm hsmall hlow hRH hQRH

theorem strict_uniform_refinement {L : ℝ} (future : 330 ≤ L) :
    rationalHeightCoefficient (8433850764/1000000000000) L < 8441646/1000000000 :=
  (rationalHeightCoefficient_antitone (by norm_num) le_rfl future).trans_lt rational_checkpoint_330

#print axioms actual_observed_read
#print axioms source_profile_point
#print axioms kernel_only_profile_point
#print axioms source_profile_ray
#print axioms source_profile_capped
#print axioms source_pi_500
#print axioms source_pi_1000
#print axioms source_pi_1000000
#print axioms strict_uniform_refinement
end SynergyHeightC.MainRationalClosed
