/- Whole unchanged C main and observed bytes supporting both300ray error bounds.
The same actual output read supplies the backward finite-sum transfer. -/
import SynergyHeightC.MainPiPsi300Read
namespace SynergyHeightC.MainPiPsi300Program
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem main_observed_pi_psi_300 (platform : WorldIO.Platform) (initial : Stream)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 300 ≤ x) :
    ∃ (trace : Nat → Stream) (final : WorldIO.World),
      trace 0=initial ∧
      WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform CompleteIOModel.policy
        3 "main" [] ⟨Initialization.initializeBoundGlobals.getD Machine.empty,initial⟩
        (WorldIO.signed32 0) ⟨FullMainPrefix.cache,final.stream⟩ ∧
      final.stream.accepted=(trace 768).accepted++MainObservedOutput.bytes ∧
      final.stream.delivered=final.stream.accepted.length ∧
      Eπ x ≤ (9354674/1000000000)*x^(-(1:ℝ)/8) ∧
      Eψ x ≤ (9354674/1000000000)*x^(-(1:ℝ)/8) := by
  obtain ⟨trace,final,out,start,source,read,bytes,delivered,sum,bound,oldMathematical⟩ :=
    MainCompleteModel.complete_source_main_and_pnt platform initial h hCHJ hrvm hsmall hlow hRH hQRH
  have consumers := MainPiPsi300Read.pi_psi_300_from_actual_total_read read
    h hCHJ hrvm hsmall hlow hRH hQRH
  have piBound := consumers.1 x hx
  have psiBound := consumers.2 x hx
  simp only [pow_zero,mul_one,show (7/8:ℝ)-1= -1/8 by norm_num] at piBound psiBound
  have observed : out=MainObservedOutput.total :=
    (MainFinalTotal.actual_read_identity read).trans MainObservedOutput.total_exact
  rw [observed] at bytes
  have actualBytes : final.stream.accepted=(trace 768).accepted++MainObservedOutput.bytes := by
    rw [MainObservedOutput.bytes_exact,←List.append_assoc]
    exact bytes
  exact ⟨trace,final,start,source,actualBytes,delivered,piBound,psiBound⟩

#print axioms main_observed_pi_psi_300
end SynergyHeightC.MainPiPsi300Program
