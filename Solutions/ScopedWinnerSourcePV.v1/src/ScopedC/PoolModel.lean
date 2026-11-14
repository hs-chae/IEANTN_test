/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.HelperCodeAdapters

namespace ScopedC.PoolModel
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Ghost heap applicability is a proposition, not an application result.
-- Classical decidability here is not a runtime/application primitive.
noncomputable section
instance contextDecidable (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high : Nat) :
    Decidable (GenericPoolContext l s cells top high) := Classical.propDecidable _

/-- A ghost specification decoder. Its successful result carries only actual
 typed heap applicability. It is not an external runtime or desired-output
 primitive; source execution is proved below using the existing body proof. -/
structure Snapshot (l : PoolLayout) (s : State) where
  cells : List (Option Value)
  top : Nat
  high : Nat
  context : GenericPoolContext l s cells top high

 def snapshot (l : PoolLayout) (s : State) : Option (Snapshot l s) := do
  let p ← s.heap[l.pool]?
  let t ← s.heap[l.top]?
  let h ← s.heap[l.high]?
  let [some (.integer tv)] := t.cells | none
  let [some (.integer hv)] := h.cells | none
  let top := tv.number.toNat
  let high := hv.number.toNat
  if hc : GenericPoolContext l s p.cells top high then some ⟨p.cells,top,high,hc⟩ else none

 theorem snapshot_complete {l : PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (h : GenericPoolContext l s cells top high) : snapshot l s = some ⟨cells,top,high,h⟩ := by
  simp [snapshot,h.pool_read,h.top_read,h.high_read,poolObject,counterObject,word,h]

 def keep (l : PoolLayout) (args : List Value) (s : State) : Option (Value × State) := do
  let [.natObject slot] := args | none
  let state ← snapshot l s
  let _ ← NatArena.read s.nats slot
  if state.top < capacity then
    some (.natObject slot,keepResult l s state.cells state.top state.high slot)
  else none

 theorem keep_sound (code : List Function) (installed : Generated.f_keep ∈ code)
    {l : PoolLayout} {args : List Value} {s t : State} {value : Value}
    (h : keep l args s = some (value,t)) :
    SourceCall Header.layout code 1 "keep" args s value t := by
  unfold keep at h
  split at h <;> try contradiction
  rename_i slot
  cases hs : snapshot l s with
  | none => simp [hs] at h
  | some state =>
    cases hr : NatArena.read s.nats slot with
    | none => simp [hs,hr] at h
    | some n =>
      have live : NatArena.Borrow s.nats slot n := by
        unfold NatArena.read at hr
        split at hr
        · exact ⟨hr,by assumption⟩
        · contradiction
      simp only [hs,hr,bind,Option.bind] at h
      split_ifs at h with hc
      · cases h
        exact ScopedC.HelperCodeAdapters.keep_for_code code installed state.context hc live

 theorem keep_complete {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot n : Nat} (h : GenericPoolContext l s cells top high)
    (hc : top < capacity) (borrow : NatArena.Borrow s.nats slot n) :
    keep l [.natObject slot] s = some (.natObject slot,keepResult l s cells top high slot) := by
  simp [keep,snapshot_complete h,NatArena.read_of_borrow borrow,hc]

 /-- The only additional successful service branch is proved actual keep.
 All runtime calls use the already enumerated generic ABI contracts. -/
 def runtimeKeep (l : PoolLayout) : Call := fun name args s =>
  match RuntimeCore.call name args s with
  | some r => some r
  | none => if name = "keep" then keep l args s else none

 theorem runtimeKeep_closed (code : List Function) (installed : Generated.f_keep ∈ code)
    (l : PoolLayout) {name : String} {args : List Value} {s t : State} {value : Value}
    (h : runtimeKeep l name args s = some (value,t)) :
    SourceCall Header.layout code 1 name args s value t := by
  unfold runtimeKeep at h
  cases hr : RuntimeCore.call name args s with
  | some r =>
    simp only [hr,Option.some.injEq] at h
    cases h
    exact runtime_leaf hr
  | none =>
    simp only [hr] at h
    split_ifs at h with hn
    · subst name
      exact keep_sound code installed h

 theorem runtimeKeep_primitive {l : PoolLayout} {name : String} {args : List Value}
    {s t : State} {value : Value} (h : RuntimeCore.call name args s = some (value,t)) :
    runtimeKeep l name args s = some (value,t) := by simp [runtimeKeep,h]

 theorem runtimeKeep_keep {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot n : Nat} (h : GenericPoolContext l s cells top high)
    (hc : top < capacity) (borrow : NatArena.Borrow s.nats slot n) :
    runtimeKeep l "keep" [.natObject slot] s = some (.natObject slot,keepResult l s cells top high slot) := by
  simp [runtimeKeep,RuntimeCore.call,RuntimeCore.binaryName,keep_complete h hc borrow]

end
end ScopedC.PoolModel
