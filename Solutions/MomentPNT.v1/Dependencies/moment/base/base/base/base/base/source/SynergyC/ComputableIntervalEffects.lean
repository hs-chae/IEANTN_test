/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.ComputableIntervalService

namespace SynergyC.ComputableIntervalService
open ScopedC ScopedC.Machine
open SynergyC.ComputableIntervalInput
set_option autoImplicit false
set_option maxHeartbeats 100000

private theorem binary_state_eq (op : ComputableIntervalBinary.Operation)
    {args : List Value} {s t : State} {v : Value}
    (h : ComputableIntervalBinary.call op args s=some (v,t)) : t=s := by
  unfold ComputableIntervalBinary.call at h
  split at h
  · rename_i x y
    cases ha : interval? x with
    | none=>simp [ha] at h
    | some a=>
      cases hb : interval? y with
      | none=>simp [ha,hb] at h
      | some b=>
        simp only[ha,hb,Bind.bind,Option.bind] at h
        split_ifs at h
        simp only[Option.some.injEq,Prod.mk.injEq] at h
        exact h.2.symm
  · contradiction

private theorem rat_state_eq {args : List Value} {s t : State} {v : Value}
    (h : ComputableIntervalMixed.rat args s=some (v,t)) : t=s := by
  unfold ComputableIntervalMixed.rat at h
  split at h
  · split_ifs at h
    simp only[Option.some.injEq,Prod.mk.injEq] at h
    exact h.2.symm
  · contradiction

private theorem divN_state_eq {args : List Value} {s t : State} {v : Value}
    (h : ComputableIntervalMixed.divN args s=some (v,t)) : t=s := by
  unfold ComputableIntervalMixed.divN at h
  split at h
  · rename_i raw n
    cases ha : interval? raw with
    | none=>simp [ha] at h
    | some a=>
      simp only[ha,Bind.bind,Option.bind] at h
      split_ifs at h
      simp only[Option.some.injEq,Prod.mk.injEq] at h
      exact h.2.symm
  · contradiction

theorem dispatch_state_eq {called : String} {args : List Value} {s t : State} {v : Value}
    (h : dispatch called args s=some (v,t)) : t=s := by
  unfold dispatch at h
  split_ifs at h
  · split at h
    · cases h;rfl
    · contradiction
  · split at h
    · cases h;rfl
    · contradiction
  · exact rat_state_eq h
  · exact divN_state_eq h
  · cases ho : ComputableIntervalBinary.operation called with
    | none=>simp [ho] at h
    | some op=>
      apply binary_state_eq op
      simpa only[ho,Bind.bind,Option.bind] using h

/-- All eight guarded source summaries preserve the whole actual state. -/
theorem state_eq {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s=some (v,t)) : t=s := by
  unfold call at h
  cases hm : ComputableArithmeticService.maxContext? s with
  | none=>simp [hm] at h
  | some maxCtx=>
    cases hs : scaleContext? s with
    | none=>simp [hm,hs] at h
    | some scaleCtx=>
      apply dispatch_state_eq
      simpa only[hm,hs,Bind.bind,Option.bind] using h

theorem preserves_nats {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s=some (v,t)) : t.nats=s.nats := congrArg State.nats (state_eq h)

end SynergyC.ComputableIntervalService
