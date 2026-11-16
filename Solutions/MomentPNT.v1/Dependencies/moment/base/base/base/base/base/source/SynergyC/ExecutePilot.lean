/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedC.SourceCallExecute
import SynergyC.Bundle
import SynergyC.Initialization
import SynergyC.SourceIntervalMath
import SynergyBasis.PositiveModel

namespace SynergyC.ExecutePilot
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames
open ScopedNumerical SynergyBasis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def hasBox (v : Value) (a : ProofBox) : Bool :=
  match v with
  | .record tag [.integer lo,.integer hi] =>
      decide (tag="I" ∧ lo.type=Word512.type ∧ hi.type=Word512.type ∧ lo.number=a.lo ∧ hi.number=a.hi)
  | _ => false

theorem hasBox_sound {v : Value} {a : ProofBox} (h : hasBox v a = true) :
    v = SourceIntervalMath.represented a := by
  unfold hasBox at h
  split at h
  · rename_i tag lo hi
    obtain ⟨ht,hl,hh,hln,hhn⟩ := of_decide_eq_true h
    cases lo with
    | mk lt ln =>
      cases hi with
      | mk ht' hn =>
        simp only at hl hh hln hhn
        subst tag
        subst lt
        subst ht'
        subst ln
        subst hn
        rfl
  · contradiction

def checked (name : String) (args : List Value) (a : ProofBox) : Bool :=
  match SourceCallExecute.execute Header.layout Bundle.code 128 512 8 name args Initialization.state with
  | some (v,_) => hasBox v a
  | none => false

theorem source_of_checked {name : String} {args : List Value} {a : ProofBox}
    (h : checked name args a = true) :
    ∃ after, SourceCall Header.layout Bundle.code 8 name args Initialization.state
      (SourceIntervalMath.represented a) after := by
  cases he : SourceCallExecute.execute Header.layout Bundle.code 128 512 8 name args Initialization.state with
  | none => simp [checked,he] at h
  | some pair =>
      rcases pair with ⟨v,t⟩
      simp only [checked,he] at h
      have hv := hasBox_sound h
      subst v
      exact ⟨t,SourceCallExecute.execute_sound he⟩

end SynergyC.ExecutePilot
