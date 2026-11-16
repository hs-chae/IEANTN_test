/- Full actual source-main/observed-output refinement. The stronger PNT profile
consumes the physical total-read witness obtained with the constructed source run.
The successful-stdio model and actual compiled-run association remain distinct. -/
import SynergyHeightC.MainRationalClosed
namespace SynergyHeightC.MainRationalProgram
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem main_observed_rational_profile (platform : WorldIO.Platform) (initial : Stream)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 330 ≤ x) :
    ∃ (trace : Nat → Stream) (final : WorldIO.World),
      trace 0=initial ∧
      WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform CompleteIOModel.policy
        3 "main" [] ⟨Initialization.initializeBoundGlobals.getD Machine.empty,initial⟩
        (WorldIO.signed32 0) ⟨FullMainPrefix.cache,final.stream⟩ ∧
      final.stream.accepted=(trace 768).accepted++MainObservedOutput.bytes ∧
      final.stream.delivered=final.stream.accepted.length ∧
      Eπ x ≤ rationalHeightCoefficient (8433850764/1000000000000) (Real.log x)*x^(-(1:ℝ)/8) := by
  obtain ⟨trace,final,out,start,source,read,bytes,delivered,sum,bound,oldMathematical⟩ :=
    MainCompleteModel.complete_source_main_and_pnt platform initial h hCHJ hrvm hsmall hlow hRH hQRH
  have mathematical := MainRationalRead.pi_rational_point_from_actual_total_read read
    SourcePointSlopesV1.All.bounds h hCHJ hrvm hsmall hlow hRH hQRH hx
  have observed : out=MainObservedOutput.total :=
    (MainFinalTotal.actual_read_identity read).trans MainObservedOutput.total_exact
  rw [observed] at bytes
  have actualBytes : final.stream.accepted=(trace 768).accepted++MainObservedOutput.bytes := by
    rw [MainObservedOutput.bytes_exact,←List.append_assoc]
    exact bytes
  exact ⟨trace,final,start,source,actualBytes,delivered,mathematical⟩

#print axioms main_observed_rational_profile
end SynergyHeightC.MainRationalProgram
