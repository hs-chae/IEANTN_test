/- Actual initializer execution with proved C contracts and a proved empty
Nat arena. This is an additive component, not a whole-main/I/O PV claim. -/
import SynergyHeightC.FullContractPointExecute
import SynergyHeightC.InitExecute
import ScopedC.NatContractEffects
namespace SynergyHeightC.FullContractInit
open ScopedC ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[irreducible] def run : Option (Value × State) :=
  ContractExecute.execute SynergyC.Header.layout Generated.functions 128 2048
    SynergyC.ComputableFullService.call 13 "initializePointConstants" [] Initialization.state

def checked : Bool := ArrayCallCheck.hasState run (InitCacheProposal.postState NatArena.empty)

theorem service_keeps : NatEffects.Preserves SynergyC.ComputableFullService.call :=
  fun _ _ _ _ _ h => SynergyC.ComputableFullService.preserves_nats h

/-- The exact actual returned arena is derived from generic source effects;
no equality of owner functions or initial application cache is assumed. -/
theorem source_empty_of_checked (h : checked = true) :
    ArraySourceCalls.SourceCall SynergyC.Header.layout Bundle.code 16
      "initializePointConstants" [] Initialization.state .unit
      (InitCacheProposal.postState NatArena.empty) := by
  obtain ⟨after,hr,shape⟩ := ArrayCallCheck.hasState_sound h
  have run_eq : run = ContractExecute.execute SynergyC.Header.layout Generated.functions 128 2048
      SynergyC.ComputableFullService.call 13 "initializePointConstants" [] Initialization.state := by
    unfold run
    rfl
  have exec := Eq.mp (congrArg (fun result => result=some (.unit,after)) run_eq) hr
  have sameArena := NatEffects.contract_execute service_keeps exec
  have emptyArena : after.nats = NatArena.empty := sameArena
  have exactState : after = InitCacheProposal.postState after.nats := shape
  rw [emptyArena] at exactState
  have actual : ArraySourceCalls.SourceCall SynergyC.Header.layout Generated.functions 16
      "initializePointConstants" [] Initialization.state .unit after :=
    ContractExecute.execute_sound (fun _ _ _ _ _ hh => FullContractPointExecute.contract_closed hh) exec
  rw [exactState] at actual
  exact Eq.mpr (congrArg (fun code => ArraySourceCalls.SourceCall SynergyC.Header.layout code
    16 "initializePointConstants" [] Initialization.state .unit
      (InitCacheProposal.postState NatArena.empty)) Bundle.code_exact) actual

#print axioms service_keeps
#print axioms source_empty_of_checked
end SynergyHeightC.FullContractInit
