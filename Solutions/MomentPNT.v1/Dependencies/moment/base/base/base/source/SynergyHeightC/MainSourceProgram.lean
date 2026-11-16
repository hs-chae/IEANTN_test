/- Full source-bound globals initialization plus the complete actual main and
same-output mathematical consumer. The runtime/compiler/ABI boundary and actual
normal-I/O conditions remain explicit; no initial application state is trusted. -/
import SynergyHeightC.MainApplication
import SynergyHeightC.BoundInitialization
namespace SynergyHeightC.MainSourceProgram
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

theorem source_initialized_main_output_and_pnt (platform : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
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
    Initialization.initializeBoundGlobals=some Initialization.state ∧
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
      HasPowerLogBound Eπ (8441646/1000000000) 0 (7/8) (Real.exp 330) :=
  ⟨Initialization.actual_source_initialization,
    MainApplication.main_output_and_pnt platform fault streams checked emitted flushed emit flush
      h hCHJ hrvm hsmall hlow hRH hQRH⟩

#print axioms source_initialized_main_output_and_pnt
end SynergyHeightC.MainSourceProgram
