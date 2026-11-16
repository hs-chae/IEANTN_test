/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.ComputableIntervalEffects
import SynergyC.ComputableArithmeticEffects
import ScopedC.CallEvents

namespace SynergyC.ComputableFullService
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 100000

/-- Eleven summaries of already proved actual source bodies. Existing scalar
code and active campaign dependencies are unchanged; this additive service
combines them with eight guarded interval source summaries. -/
def call : Call := CallEvents.append ComputableArithmeticService.call ComputableIntervalService.call

theorem closed (code : List Function) (lib : ComputableIntervalService.Library code)
    {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s=some (v,t)) :
    SourceCall Header.layout code 3 called args s v t :=
  CallEvents.append_closed
    (fun _ _ _ _ _ h=>raise_once (ComputableArithmeticService.closed code lib.addU lib.mulU lib.ceilDiv lib.arithmeticParameters h))
    (fun _ _ _ _ _ h=>ComputableIntervalService.closed code lib h) h

theorem array_closed (code : List Function) (lib : ComputableIntervalService.Library code)
    {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s=some (v,t)) :
    ArraySourceCalls.SourceCall Header.layout code 3 called args s v t :=
  ArrayLegacyLift.source_call (closed code lib h)

theorem state_eq {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s=some (v,t)) : t=s := by
  unfold call CallEvents.append at h
  cases hs : ComputableArithmeticService.call called args s with
  | none=>
    apply ComputableIntervalService.state_eq
    simpa only[hs] using h
  | some answer=>
    simp only[hs,Option.some.injEq] at h
    cases h
    exact ComputableArithmeticService.state_eq hs

theorem preserves_nats {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s=some (v,t)) : t.nats=s.nats := congrArg State.nats (state_eq h)

end SynergyC.ComputableFullService
