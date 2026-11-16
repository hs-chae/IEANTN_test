/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.ComputableIntervalBinary
import SynergyC.ComputableIntervalMixed

namespace SynergyC.ComputableIntervalService
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames
open SynergyC.ComputableIntervalInput
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

/-- The eight interval operations are summaries of their existing proved
source bodies. All arithmetic/domain failures return none and must be handled
by the caller's ordinary source interpreter, never accepted as an answer. -/
def dispatch : Call := fun called args s=>
  if called="zero" then
    match args with | []=>some (ZeroBody.zeros,s) | _=>none
  else if called="unit" then
    match args with | []=>some (UnitBody.result,s) | _=>none
  else if called="rat" then ComputableIntervalMixed.rat args s
  else if called="divN" then ComputableIntervalMixed.divN args s
  else do
    let op←ComputableIntervalBinary.operation called
    ComputableIntervalBinary.call op args s

/-- Context guards inspect actual MAXU/S memory. Every executed decision is
constructive: no classical application-state predicate or output oracle. -/
def call : Call := fun called args s=>do
  let _←ComputableArithmeticService.maxContext? s
  let _←scaleContext? s
  dispatch called args s

theorem dispatch_closed (code : List Function) (lib : Library code)
    {s t : State} (maxCtx : MaxContext s) (scaleCtx : UnitBody.ScaleContext s)
    {called : String} {args : List Value} {v : Value}
    (h : dispatch called args s=some (v,t)) :
    SourceCall Header.layout code 3 called args s v t := by
  unfold dispatch at h
  split_ifs at h with hz hu hr hd
  · subst called
    split at h
    · cases h
      exact raise_once (raise_once (ZeroBody.source_zero code lib.zero s))
    · contradiction
  · subst called
    split at h
    · cases h
      exact raise_once (raise_once (UnitBody.source_unit code lib.unit scaleCtx))
    · contradiction
  · subst called
    exact ComputableIntervalMixed.rat_closed code lib maxCtx scaleCtx h
  · subst called
    exact ComputableIntervalMixed.divN_closed code lib maxCtx h
  · cases ho : ComputableIntervalBinary.operation called with
    | none=>simp [ho] at h
    | some op=>
      have accepted : ComputableIntervalBinary.call op args s=some (v,t) := by
        simpa only[ho,Bind.bind,Option.bind] using h
      have named:=ComputableIntervalBinary.operation_name ho
      rw[named]
      exact ComputableIntervalBinary.closed code lib op maxCtx scaleCtx accepted

theorem closed (code : List Function) (lib : Library code)
    {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s=some (v,t)) :
    SourceCall Header.layout code 3 called args s v t := by
  unfold call at h
  cases hm : ComputableArithmeticService.maxContext? s with
  | none=>simp [hm] at h
  | some maxCtx=>
    cases hs : scaleContext? s with
    | none=>simp [hm,hs] at h
    | some scaleCtx=>
      apply dispatch_closed code lib maxCtx scaleCtx
      simpa only[hm,hs,Bind.bind,Option.bind] using h

theorem array_closed (code : List Function) (lib : Library code)
    {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s=some (v,t)) :
    ArraySourceCalls.SourceCall Header.layout code 3 called args s v t :=
  ArrayLegacyLift.source_call (closed code lib h)

end SynergyC.ComputableIntervalService
