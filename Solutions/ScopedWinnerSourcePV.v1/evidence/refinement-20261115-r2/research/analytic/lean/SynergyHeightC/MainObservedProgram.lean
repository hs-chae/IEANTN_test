/- A complete source-main model whose final delivered interval bytes equal the
fresh physical C observation. Compiler/runtime/source/run association is separately
recorded; these observations never replace the source numerical computation. -/
import SynergyHeightC.MainObservedOutput
namespace SynergyHeightC.MainObservedProgram
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

theorem complete_source_main_observed_and_pnt (platform : WorldIO.Platform) (initial : Stream)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    ∃ (trace : Nat → Stream) (final : WorldIO.World),
      trace 0=initial ∧
      WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform CompleteIOModel.policy
        3 "main" [] ⟨Initialization.initializeBoundGlobals.getD Machine.empty,initial⟩
        (WorldIO.signed32 0) ⟨FullMainPrefix.cache,final.stream⟩ ∧
      final.stream.accepted=(trace 768).accepted++MainObservedOutput.bytes ∧
      final.stream.delivered=final.stream.accepted.length ∧
      prefixSum logCellCount=some MainObservedOutput.total ∧
      realWord MainObservedOutput.total.hi ≤ 8433850764/1000000000000 ∧
      HasPowerLogBound Eπ (8441646/1000000000) 0 (7/8) (Real.exp 330) := by
  obtain ⟨trace,final,out,start,source,read,bytes,delivered,sum,bound,mathematical⟩ :=
    MainCompleteModel.complete_source_main_and_pnt platform initial h hCHJ hrvm hsmall hlow hRH hQRH
  have observed : out=MainObservedOutput.total :=
    (MainFinalTotal.actual_read_identity read).trans MainObservedOutput.total_exact
  rw [observed] at bytes sum bound
  have actualBytes : final.stream.accepted=(trace 768).accepted++MainObservedOutput.bytes := by
    rw [MainObservedOutput.bytes_exact,←List.append_assoc]
    exact bytes
  exact ⟨trace,final,start,source,actualBytes,delivered,sum,bound,mathematical⟩

#print axioms complete_source_main_observed_and_pnt
end SynergyHeightC.MainObservedProgram
