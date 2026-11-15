/- A complete constructed source-main execution in a concrete successful-stdio
model, with no remaining application/I/O trace premises. This is a modeled
scenario; actual host/source/build/run association is recorded separately. -/
import SynergyHeightC.MainIOTrace
import SynergyHeightC.MainComputedGlobals
namespace SynergyHeightC.MainCompleteModel
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

theorem complete_source_main_and_pnt (platform : WorldIO.Platform) (initial : Stream)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    ∃ (trace : Nat → Stream) (final : WorldIO.World) (out : ProofBox),
      trace 0=initial ∧
      WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform CompleteIOModel.policy
        3 "main" [] ⟨Initialization.initializeBoundGlobals.getD Machine.empty,initial⟩
        (WorldIO.signed32 0) ⟨FullMainPrefix.cache,final.stream⟩ ∧
      evalExpr SynergyC.Header.layout FullMainPrefix.service 1
        (FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) (.var "total")=
        some (SynergyC.SourceIntervalMath.represented out,
          FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) ∧
      final.stream.accepted=(trace 768).accepted++
        EmitUBuffer.bytes out.lo++EmitUBuffer.bytes out.hi ∧
      final.stream.delivered=final.stream.accepted.length ∧
      prefixSum logCellCount=some out ∧
      realWord out.hi ≤ 8433850764/1000000000000 ∧
      HasPowerLogBound Eπ (8441646/1000000000) 0 (7/8) (Real.exp 330) := by
  let trace := MainIOTrace.streams initial
  let total := SourceMainBudgetV1.Data.total 768
  let state := FullMainEdges.loopState total 768
  let emitted : WorldIO.World := ⟨state,CompleteIOModel.appendWord
    (CompleteIOModel.appendWord (trace 768) total.lo) total.hi⟩
  let final : WorldIO.World := ⟨emitted.app,
    {emitted.stream with delivered:=emitted.stream.accepted.length}⟩
  have emit : EmitIService.call platform CompleteIOModel.policy "emitI"
      [SynergyC.SourceIntervalMath.represented total] ⟨state,trace 768⟩=some (.unit,emitted) :=
    CompleteIOModel.emitI_success platform state total MainFinalTotal.source_total_representable
      (trace 768) rfl
  have flush : WorldIO.stdio platform CompleteIOModel.policy "fflush"
      [WorldIO.stdoutValue platform] emitted=some (WorldIO.signed32 0,final) :=
    CompleteIOModel.flush_success platform emitted
  obtain ⟨out,source,read,bytes,delivered,sum,bound,mathematical⟩ :=
    MainComputedGlobals.main_from_computed_source_globals platform CompleteIOModel.policy trace
      (MainIOTrace.checked_rows platform initial) emitted final emit flush
      h hCHJ hrvm hsmall hlow hRH hQRH
  refine ⟨trace,final,out,rfl,?_,read,bytes,delivered,sum,bound,mathematical⟩
  exact source

#print axioms complete_source_main_and_pnt
end SynergyHeightC.MainCompleteModel
