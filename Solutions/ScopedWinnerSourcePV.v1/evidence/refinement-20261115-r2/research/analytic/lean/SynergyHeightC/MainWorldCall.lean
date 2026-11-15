/- Complete installed source main call, using only actual-source callbacks.
Its checked normal-I/O conditions remain explicit, not generic platform successes. -/
import SynergyHeightC.MainWorldMain
import ScopedIO.WorldInstalled
namespace SynergyHeightC.MainWorldCall
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical ScopedIO
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

theorem installed : Generated.f_main∈Bundle.code := by
  rw [Bundle.code_exact]
  exact List.mem_of_getElem? (show Generated.functions[38]?=some Generated.f_main by rfl)

theorem pop_cache : Machine.popScope Initialization.state FullMainPrefix.cache=FullMainPrefix.cache := by
  have length : InitCacheProposal.heap.length=14 := by rfl
  simp [Machine.popScope,Initialization.state,FullMainPrefix.cache,InitCacheProposal.postState,length]

theorem return_cast (state : State) :
    castValue SynergyC.Header.layout state 100 "int" (WorldIO.signed32 0)=
      some (WorldIO.signed32 0) := by rfl

theorem source_main (platform : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    (streams : Nat → Stream) (checked : MainWorldLoop.CheckedRowCalls platform fault streams)
    (ranges : SynergyC.SourceIntervalMath.representable (SourceMainBudgetV1.Data.total 768))
    (emitted flushed : WorldIO.World)
    (emit : EmitIService.call platform fault "emitI"
      [SynergyC.SourceIntervalMath.represented (SourceMainBudgetV1.Data.total 768)]
      ⟨FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768,streams 768⟩=
      some (.unit,emitted))
    (flush : WorldIO.stdio platform fault "fflush" [WorldIO.stdoutValue platform] emitted=
      some (WorldIO.signed32 0,flushed)) :
    WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform fault 3 "main" []
      ⟨Initialization.state,streams 0⟩ (WorldIO.signed32 0)
      ⟨FullMainPrefix.cache,flushed.stream⟩ := by
  have body := (MainWorldMain.actual_body platform fault streams checked ranges
    emitted flushed emit flush).1
  have finish : WorldSource.Finish SynergyC.Header.layout Generated.f_main
      ⟨Initialization.state,streams 0⟩
      (.returned ⟨FullMainPrefix.cache,flushed.stream⟩ (WorldIO.signed32 0))
      (WorldIO.signed32 0) ⟨FullMainPrefix.cache,flushed.stream⟩ := by
    refine ⟨return_cast FullMainPrefix.cache,?_⟩
    change (⟨FullMainPrefix.cache,flushed.stream⟩ : WorldIO.World)=
      ⟨Machine.popScope Initialization.state FullMainPrefix.cache,flushed.stream⟩
    rw [pop_cache]
  exact WorldSource.installed_body (cfg:=SynergyC.Header.layout) (code:=Bundle.code)
    (p:=platform) (fault:=fault) (rank:=2) (f:=Generated.f_main) (args:=[])
    (s:=⟨Initialization.state,streams 0⟩) (t:=⟨FullMainPrefix.cache,flushed.stream⟩)
    (v:=WorldIO.signed32 0) (frame:=Initialization.state)
    (pure:=FullMainPrefix.service) (service:=MainWorldService.call platform fault)
    (outcome:=.returned ⟨FullMainPrefix.cache,flushed.stream⟩ (WorldIO.signed32 0))
    installed (fun _ _ _ _ _ accepted=>⟨16,FullMainPrefix.service_closed accepted⟩)
    (fun _ _ _ _ _ accepted=>MainWorldService.closed platform fault accepted)
    MainWorldStart.actual_main_arguments body finish

#print axioms installed
#print axioms pop_cache
#print axioms return_cast
#print axioms source_main
end SynergyHeightC.MainWorldCall
