/- The complete actual source main emits and delivers the same interval whose
physical memory read supplies the ANT consumer. Checked I/O normal-path
conditions and the original analytic assumptions are explicit. -/
import SynergyHeightC.MainWorldCall
import SynergyHeightC.MainFinalTotal
namespace SynergyHeightC.MainApplication
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

theorem main_output_and_pnt (platform : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    (streams : Nat → Stream) (checked : MainWorldLoop.CheckedRowCalls platform fault streams)
    (emitted flushed : WorldIO.World)
    (emit : EmitIService.call platform fault "emitI"
      [SynergyC.SourceIntervalMath.represented (SourceMainBudgetV1.Data.total 768)]
      ⟨FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768,streams 768⟩=
      some (.unit,emitted))
    (flush : WorldIO.stdio platform fault "fflush" [WorldIO.stdoutValue platform] emitted=
      some (WorldIO.signed32 0,flushed))
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    ∃ out : ProofBox,
      WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform fault 3 "main" []
        ⟨Initialization.state,streams 0⟩ (WorldIO.signed32 0)
        ⟨FullMainPrefix.cache,flushed.stream⟩ ∧
      evalExpr SynergyC.Header.layout FullMainPrefix.service 1
        (FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) (.var "total")=
        some (SynergyC.SourceIntervalMath.represented out,
          FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) ∧
      flushed.stream.accepted=(streams 768).accepted++
        EmitUBuffer.bytes out.lo++EmitUBuffer.bytes out.hi ∧
      flushed.stream.delivered=flushed.stream.accepted.length ∧
      prefixSum logCellCount=some out ∧
      realWord out.hi ≤ 8433850764/1000000000000 ∧
      HasPowerLogBound Eπ (8441646/1000000000) 0 (7/8) (Real.exp 330) := by
  let out := SourceMainBudgetV1.Data.total 768
  have range : SynergyC.SourceIntervalMath.representable out :=
    MainFinalTotal.source_total_representable
  have actualSource := MainWorldCall.source_main platform fault streams checked range
    emitted flushed emit flush
  have emittedSource := MainWorldMain.actual_body platform fault streams checked range
    emitted flushed emit flush
  have read : evalExpr SynergyC.Header.layout FullMainPrefix.service 1
      (FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) (.var "total")=
      some (SynergyC.SourceIntervalMath.represented out,
        FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) :=
    MainTotalOutput.read_total FullMainPrefix.service out 768
  have mathematical := MainFinalTotal.pi_from_actual_total_read (box:=out) read
    h hCHJ hrvm hsmall hlow hRH hQRH
  exact ⟨out,actualSource,read,emittedSource.2.1,emittedSource.2.2,
    MainBudgetSourceSum.prefix_value 768 (by decide),MainFinalTotal.source_total_word_bound,
    mathematical⟩

#print axioms main_output_and_pnt
end SynergyHeightC.MainApplication
