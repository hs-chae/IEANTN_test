/- Actual main prefix, preserving its local variables for the following loop.
This is a statement-sequence component, not a replacement main or an I/O claim. -/
import SynergyHeightC.FullContractInit
import SynergyHeightC.MainPrefix
import ScopedC.ArrayStages
namespace SynergyHeightC.FullMainPrefix
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical ScopedNumerical.ProofBox
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def service : Call := ContractExecute.execute SynergyC.Header.layout Generated.functions
  128 2048 SynergyC.ComputableFullService.call 13

def statements : List Stmt := (PointExecuteAPI.mainStatements.drop 1).take 5

theorem actual_main_init_statement : PointExecuteAPI.mainStatements[0]? =
    some (.eval (.call (.var "initializePointConstants") [])) := by rfl

theorem actual_main_prefix : PointExecuteAPI.mainStatements.take 6 =
    .eval (.call (.var "initializePointConstants") []) :: statements := by rfl

def unsigned32 (n : Nat) : Value := .integer ⟨⟨false,32⟩,(n:ℤ)⟩
def cache : State := InitCacheProposal.postState NatArena.empty

def afterCells : State := allocate cache "const unsigned int" "cells" (some (unsigned32 768))
def afterHeight : State := allocate afterCells "I" "h"
  (some (SynergyC.SourceIntervalMath.represented SynergyAnalytic.HeightPoint.hValue))
def afterSpan : State := allocate afterHeight "I" "span"
  (some (SynergyC.SourceIntervalMath.represented MainPrefix.spanValue))
def afterTotal : State := allocate afterSpan "I" "total"
  (some (SynergyC.SourceIntervalMath.represented (⟨0,0⟩:ProofBox)))
def prefixState : State := allocate afterTotal "unsigned int" "i" (some (unsigned32 0))

@[irreducible] def run : Option ArraySourceExecute.Outcome :=
  ArraySourceExecute.statements SynergyC.Header.layout service 128 2048 statements cache

def checked : Bool := ArrayStages.hasNext run prefixState

theorem service_closed {name : String} {args : List Value} {s t : State} {v : Value}
    (h : service name args s = some (v,t)) :
    ArraySourceCalls.SourceCall SynergyC.Header.layout Bundle.code 16 name args s v t := by
  have he : ContractExecute.execute SynergyC.Header.layout Generated.functions 128 2048
      SynergyC.ComputableFullService.call 13 name args s = some (v,t) := h
  have actual : ArraySourceCalls.SourceCall SynergyC.Header.layout Generated.functions 16
      name args s v t :=
    ContractExecute.execute_sound (fun _ _ _ _ _ hh => FullContractPointExecute.contract_closed hh) he
  exact Eq.mpr (congrArg (fun code => ArraySourceCalls.SourceCall SynergyC.Header.layout code
    16 name args s v t) Bundle.code_exact) actual

theorem service_keeps : NatEffects.Preserves service :=
  NatEffects.contract_all SynergyC.Header.layout Generated.functions 128 2048
    SynergyC.ComputableFullService.call FullContractInit.service_keeps 13

/-- The proposed prefix state is accepted only after executing the exact
five source declarations and matching all memory. No scope pop discards them. -/
theorem prefix_of_checked (h : checked = true) :
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout service)
      (ArraySourceCalls.Declare SynergyC.Header.layout service) truth ArraySourceCalls.Scope
      statements cache (.continuing prefixState) := by
  obtain ⟨arena,he⟩ := ArrayStages.hasNext_sound h
  have run_eq : run = ArraySourceExecute.statements SynergyC.Header.layout service
      128 2048 statements cache := by unfold run; rfl
  have exec := Eq.mp (congrArg (fun result => result=some
    (.continuing (ArrayStages.withArena prefixState arena))) run_eq) he
  have arena_eq := (NatEffects.statements_effect SynergyC.Header.layout service service_keeps 128 2048).2.1
    statements cache (.continuing (ArrayStages.withArena prefixState arena)) exec
  have empty : arena = NatArena.empty := arena_eq
  have same : ArrayStages.withArena prefixState arena = prefixState := by rw [empty]; rfl
  rw [same] at exec
  exact (ArraySourceExecute.sound SynergyC.Header.layout service 128 2048).2.1
    statements cache (.continuing prefixState) exec

#print axioms actual_main_prefix
#print axioms service_closed
#print axioms service_keeps
#print axioms prefix_of_checked
end SynergyHeightC.FullMainPrefix
