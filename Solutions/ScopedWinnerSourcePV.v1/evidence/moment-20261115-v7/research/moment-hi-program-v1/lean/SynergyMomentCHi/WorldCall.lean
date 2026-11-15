/- Installed actual new C entry. Every application callback retains its
existing finite source tree under the proved code inclusion. Concrete row
executions and the actual checked I/O trace must still discharge the inputs. -/
import SynergyMomentCHi.WorldMain
import SynergyHeightC.MainWorldCall
import ScopedC.SourceCallExtension

namespace SynergyMomentCHi.WorldCall
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical ScopedIO SynergyHeightC SynergyMomentC
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

theorem installed (kind : Kind) : entry kind ∈ code kind :=
  List.mem_append_right _ (List.mem_singleton_self _)

theorem old_world_preserved (kind : Kind) (platform : WorldIO.Platform)
    (fault : WorldIO.FaultPolicy) {rank : Nat} {name : String} {args : List Value}
    {s t : WorldIO.World} {v : Value}
    (old : WorldSource.SourceCall SynergyC.Header.layout SynergyHeightC.Bundle.code
      platform fault rank name args s v t) :
    WorldSource.SourceCall SynergyC.Header.layout (code kind) platform fault rank name args s v t :=
  WorldSource.code_extension (fun _ member => List.mem_append_left _ member) old

theorem source_main (kind : Kind) (platform : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    (totals : Nat → ProofBox) (zero : totals 0=⟨0,0⟩) (streams : Nat → Stream)
    (rows : ∀ i,i<768 → WorldLoop.RowRun kind platform fault totals streams i)
    (ranges : SynergyC.SourceIntervalMath.representable (totals 768))
    (emitted flushed : WorldIO.World)
    (emit : EmitIService.call platform fault "emitI"
      [SynergyC.SourceIntervalMath.represented (totals 768)]
      ⟨FullMainEdges.loopState (totals 768) 768,streams 768⟩=some (.unit,emitted))
    (flush : WorldIO.stdio platform fault "fflush" [WorldIO.stdoutValue platform] emitted=
      some (WorldIO.signed32 0,flushed)) :
    WorldSource.SourceCall SynergyC.Header.layout (code kind) platform fault 3 "__wrap_main" []
      ⟨Initialization.state,streams 0⟩ (WorldIO.signed32 0)
      ⟨FullMainPrefix.cache,flushed.stream⟩ := by
  have body := (WorldMain.actual_body kind platform fault totals zero streams rows ranges
    emitted flushed emit flush).1
  have finish : WorldSource.Finish SynergyC.Header.layout (entry kind)
      ⟨Initialization.state,streams 0⟩
      (.returned ⟨FullMainPrefix.cache,flushed.stream⟩ (WorldIO.signed32 0))
      (WorldIO.signed32 0) ⟨FullMainPrefix.cache,flushed.stream⟩ := by
    refine ⟨MainWorldCall.return_cast FullMainPrefix.cache,?_⟩
    change (⟨FullMainPrefix.cache,flushed.stream⟩ : WorldIO.World)=
      ⟨Machine.popScope Initialization.state FullMainPrefix.cache,flushed.stream⟩
    rw [MainWorldCall.pop_cache]
  exact WorldSource.installed_body (cfg:=SynergyC.Header.layout) (code:=code kind)
    (p:=platform) (fault:=fault) (rank:=2) (f:=entry kind) (args:=[])
    (s:=⟨Initialization.state,streams 0⟩) (t:=⟨FullMainPrefix.cache,flushed.stream⟩)
    (v:=WorldIO.signed32 0) (frame:=Initialization.state)
    (pure:=FullMainPrefix.service) (service:=MainWorldService.call platform fault)
    (outcome:=.returned ⟨FullMainPrefix.cache,flushed.stream⟩ (WorldIO.signed32 0))
    (installed kind)
    (fun _ _ _ _ _ accepted => ⟨16,old_execution_preserved kind
      (FullMainPrefix.service_closed accepted)⟩)
    (fun _ _ _ _ _ accepted => old_world_preserved kind platform fault
      (MainWorldService.closed platform fault accepted))
    MainWorldStart.actual_main_arguments body finish

#print axioms installed
#print axioms old_world_preserved
#print axioms source_main
end SynergyMomentCHi.WorldCall
