/- Operational join of the accepted actual C initializer and the actual
main declarations. This does not claim the loop or the I/O is completed. -/
import SynergyHeightC.FullContractInitInstance
import SynergyHeightC.FullMainPrefixInstance
namespace SynergyHeightC.FullMainInitialization
open ScopedC ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem init_operational_of_checked (h : FullContractInit.checked=true) :
    FullContractInit.run = some (.unit,FullMainPrefix.cache) := by
  obtain ⟨after,hr,shape⟩ := ArrayCallCheck.hasState_sound (result:=FullContractInit.run)
    (cache:=InitCacheProposal.postState NatArena.empty) h
  have run_eq : FullContractInit.run = ContractExecute.execute SynergyC.Header.layout Generated.functions
      128 2048 SynergyC.ComputableFullService.call 13 "initializePointConstants" [] Initialization.state := by
    unfold FullContractInit.run; rfl
  have exec := Eq.mp (congrArg (fun result=>result=some (.unit,after)) run_eq) hr
  have sameArena := NatEffects.contract_execute FullContractInit.service_keeps exec
  have emptyArena : after.nats = NatArena.empty := sameArena
  have exactState : after = InitCacheProposal.postState after.nats := shape
  rw [emptyArena] at exactState
  rw [exactState] at hr
  exact hr

theorem init_operational : FullContractInit.run = some (.unit,FullMainPrefix.cache) :=
  init_operational_of_checked FullContractInit.checked_init

theorem service_init : FullMainPrefix.service "initializePointConstants" [] Initialization.state =
    some (.unit,FullMainPrefix.cache) := by
  have eq : FullContractInit.run = FullMainPrefix.service "initializePointConstants" [] Initialization.state := by
    unfold FullContractInit.run; rfl
  exact Eq.mp (congrArg (fun r=>r=some (.unit,FullMainPrefix.cache)) eq) init_operational

theorem call_statement {cfg : Layout} {call : Call} {name : String} {s t : State}
    (h : call name [] s=some (.unit,t)) :
    ArraySourceCalls.Run cfg call (.eval (.call (.var name) [])) s (.continuing t) := by
  apply Loops.StmtRun.evaluate
  refine ⟨4,?_⟩
  change call name [] s = _
  exact h

theorem actual_init_statement : ArraySourceCalls.Run SynergyC.Header.layout FullMainPrefix.service
    (.eval (.call (.var "initializePointConstants") [])) Initialization.state
    (.continuing FullMainPrefix.cache) := call_statement service_init

theorem actual_main_first_six :
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
      (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service) truth ArraySourceCalls.Scope
      (PointExecuteAPI.mainStatements.take 6) Initialization.state
      (.continuing FullMainPrefix.prefixState) := by
  rw [FullMainPrefix.actual_main_prefix]
  exact Loops.SeqRun.next actual_init_statement FullMainPrefix.actual_source_prefix

#print axioms init_operational
#print axioms service_init
#print axioms actual_main_first_six
end SynergyHeightC.FullMainInitialization
