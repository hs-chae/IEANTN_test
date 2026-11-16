/- Generic source effects: ordinary C memory operations preserve the separate
   Nat-runtime arena; only an explicitly supplied call service can change it. -/
import ScopedC.ArraySourceCallExecute
namespace ScopedC.NatEffects
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

def Preserves (call : Call) : Prop :=
  ∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats

theorem allocate_nats (s : State) (type name : String) (v : Option Value) :
    (allocate s type name v).nats = s.nats := rfl

theorem allocateArray_nats (s : State) (type name : String) (n : Nat) :
    (ArrayDeclarations.allocateArray s type name n).nats = s.nats := rfl

theorem write_nats {cfg : Layout} {s : State} {a : Address} {w : Bool}
    {v out : Value} {t : State} (h : write cfg s a w v = some (out,t)) :
    t.nats = s.nats := by
  simp only [write,Bind.bind,Option.bind,Pure.pure] at h
  repeat' (split at h <;> simp_all)
  all_goals exact (congrArg State.nats h.2).symm

theorem foldState {α : Type} (step : State → α → Option State)
    (keeps : ∀ s a t, step s a = some t → t.nats = s.nats)
    (xs : List α) {s t : State} (h : xs.foldlM step s = some t) : t.nats = s.nats := by
  induction xs generalizing s with
  | nil => simpa using (congrArg State.nats (Option.some.inj h)).symm
  | cons x xs ih =>
      change (step s x).bind (fun u => xs.foldlM step u) = some t at h
      cases hs : step s x with
      | none => simp [hs] at h
      | some u =>
          have ht : xs.foldlM step u = some t := by simpa only [hs,Option.bind_some] using h
          exact (ih ht).trans (keeps s x u hs)

theorem foldPair {α β : Type} (step : (α × State) → β → Option (α × State))
    (keeps : ∀ acc x result, step acc x = some result → result.2.nats = acc.2.nats)
    (xs : List β) {acc out : α × State} (h : xs.foldlM step acc = some out) :
    out.2.nats = acc.2.nats := by
  induction xs generalizing acc with
  | nil => simpa using (congrArg (fun p : α × State => p.2.nats) (Option.some.inj h)).symm
  | cons x xs ih =>
      change (step acc x).bind (fun u => xs.foldlM step u) = some out at h
      cases hs : step acc x with
      | none => simp [hs] at h
      | some u =>
          have ht : xs.foldlM step u = some out := by simpa only [hs,Option.bind_some] using h
          exact (ih ht).trans (keeps acc x u hs)

#print axioms write_nats
#print axioms foldState
#print axioms foldPair
end ScopedC.NatEffects
