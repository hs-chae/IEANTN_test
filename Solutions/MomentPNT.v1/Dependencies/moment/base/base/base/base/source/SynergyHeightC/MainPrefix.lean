/- Finite actual-source prefix components, conditional on the cached state.
   Actual initialization and main sequencing remain separate obligations. -/
import ScopedC.ArraySourceCallExecute
import ScopedC.StateWordEquality
import SynergyHeightC.Bundle
import SynergyHeightC.InitCacheReadback
import SynergyC.ExecutePilot
import SynergyAnalytic.HeightPointLogGridDefs

namespace SynergyHeightC.MainPrefix
open ScopedC ScopedC.Machine
open ScopedNumerical ScopedNumerical.ProofBox
open SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def heightInput : ProofBox := literal 128 3000000000000 1
def sixtyInput : ProofBox := literal 128 60 1
def spanValue : ProofBox := sub sixtyInput SynergyAnalytic.HeightPoint.hValue

def checked (arena : NatArena.Arena) (name : String)
    (args : List Value) (expected : ProofBox) : Bool :=
  match ArraySourceCallExecute.execute SynergyC.Header.layout Bundle.code 128 1024 12
      name args (InitCacheProposal.postState arena) with
  | none => false
  | some (v,after) =>
      SynergyC.ExecutePilot.hasBox v expected &&
        StateWordEquality.stateEq 8 after (InitCacheProposal.postState after.nats)

theorem source_of_checked {arena : NatArena.Arena} {name : String}
    {args : List Value} {expected : ProofBox}
    (h : checked arena name args expected = true) :
    ∃ after, ArraySourceCalls.SourceCall SynergyC.Header.layout Bundle.code 12
      name args (InitCacheProposal.postState arena)
      (SynergyC.SourceIntervalMath.represented expected) after ∧
      after = InitCacheProposal.postState after.nats := by
  cases he : ArraySourceCallExecute.execute SynergyC.Header.layout Bundle.code 128 1024 12
      name args (InitCacheProposal.postState arena) with
  | none => simp [checked,he] at h
  | some pair =>
      rcases pair with ⟨v,after⟩
      simp only [checked,he] at h
      obtain ⟨hv,hs⟩ := StateWordEquality.split_and h
      have output := SynergyC.ExecutePilot.hasBox_sound hv
      have state := StateWordEquality.stateEq_sound hs
      refine ⟨after,?_,?_⟩
      · rw [←output]
        exact ArraySourceCallExecute.execute_sound he
      · exact state

#print axioms source_of_checked
#print axioms ScopedC.ArrayDeclarations.one_legacy
#print axioms ScopedC.ArrayDeclarations.all_legacy
#print axioms ScopedC.ArraySourceExecute.statement_sound
#print axioms ScopedC.ArraySourceCallExecute.execute_sound
end SynergyHeightC.MainPrefix
