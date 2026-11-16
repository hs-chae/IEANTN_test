/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.ComputableArithmeticService

namespace SynergyC.ComputableArithmeticService
open ScopedC ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 100000

/-- Successful summaries leave the entire actual state unchanged. This
effect theorem is derived from executable code, not a platform assumption. -/
theorem state_eq {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s=some (v,t)) : t=s := by
  unfold call at h
  cases ho : ArithmeticService.operation called with
  | none => simp [ho] at h
  | some op =>
    simp only [ho,Bind.bind,Option.bind] at h
    split at h
    · cases hc : maxContext? s with
      | none => simp [hc] at h
      | some ctx =>
        simp only [hc] at h
        split_ifs at h
        simp only [Option.some.injEq,Prod.mk.injEq] at h
        exact h.2.symm
    · contradiction

theorem preserves_nats {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s=some (v,t)) : t.nats=s.nats :=
  congrArg State.nats (state_eq h)

end SynergyC.ComputableArithmeticService
