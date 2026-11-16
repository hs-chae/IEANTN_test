/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.ComputableIntervalInput
import SynergyC.ComputableIntervalLibrary

namespace SynergyC.ComputableIntervalBinary
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames
open SynergyC.ComputableIntervalInput
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

inductive Operation where | add | mul | divI | positiveSub
  deriving DecidableEq
def name : Operation→String
  | .add=>"add" | .mul=>"mul" | .divI=>"divI" | .positiveSub=>"positiveSub"
def operation : String→Option Operation
  | "add"=>some .add | "mul"=>some .mul | "divI"=>some .divI | "positiveSub"=>some .positiveSub | _=>none
theorem operation_name {called : String} {op : Operation} (h : operation called=some op) : called=name op := by
  cases op <;> unfold operation at h <;> split at h <;> simp_all [name]

def extra (op : Operation) (a b : Bounds) : Prop := match op with
  | .add=>Range (a.lo+b.lo) ∧ Range (a.hi+b.hi)
  | .mul=>Range (a.lo*b.lo) ∧ Range (a.hi*b.hi)
  | .divI=>0<b.lo ∧ 0<b.hi ∧ Range (a.lo*UnitBody.scale) ∧ Range (a.hi*UnitBody.scale)
  | .positiveSub=>True
def allowed (op : Operation) (a b : Bounds) : Prop :=
  Range a.lo ∧ Range a.hi ∧ Range b.lo ∧ Range b.hi ∧ extra op a b
local instance (n : Int) : Decidable (Range n) := by unfold Range;infer_instance
local instance (op : Operation) (a b : Bounds) : Decidable (extra op a b) := by
  cases op <;> unfold extra <;> infer_instance
local instance (op : Operation) (a b : Bounds) : Decidable (allowed op a b) := by unfold allowed;infer_instance

def result (op : Operation) (a b : Bounds) : Value := match op with
  | .add=>ZeroBody.interval (a.lo+b.lo) (a.hi+b.hi)
  | .mul=>IntervalMulBody.result a.lo a.hi b.lo b.hi
  | .divI=>IntervalDivBody.result a.lo a.hi b.lo b.hi
  | .positiveSub=>ZeroBody.interval (PositiveSubBody.difference a.lo b.hi) (PositiveSubBody.difference a.hi b.lo)

def call (op : Operation) : List Value→State→Option (Value×State) := fun args s=>do
  let [x,y]:=args | none
  let a←interval? x
  let b←interval? y
  if allowed op a.val b.val then some (result op a.val b.val,s) else none

/-- Successful guarded summaries execute the same actual installed bodies.
The input decoder carries exact physical source-record identity. -/
theorem closed (code : List Function) (lib : ComputableIntervalService.Library code)
    (op : Operation) {s t : State} (maxCtx : MaxContext s) (scaleCtx : UnitBody.ScaleContext s)
    {args : List Value} {v : Value} (h : call op args s=some (v,t)) :
    SourceCall Header.layout code 3 (name op) args s v t := by
  unfold call at h
  split at h
  · rename_i x y
    cases ha : interval? x with
    | none=>simp [ha] at h
    | some a=>
      cases hb : interval? y with
      | none=>simp [ha,hb] at h
      | some b=>
        simp only[ha,hb,Bind.bind,Option.bind] at h
        split_ifs at h with good
        simp only[Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        rcases a with ⟨a,ax⟩
        rcases b with ⟨b,bx⟩
        change SourceCall Header.layout code 3 (name op) [x,y] s (result op a b) s
        change allowed op a b at good
        rw[ax,bx]
        rcases good with ⟨al,ah,bl,bh,domain⟩
        cases op with
        | add=>
          exact raise_once (IntervalAddBody.source_add code lib.add lib.addU maxCtx al ah bl bh domain.1 domain.2)
        | mul=>
          exact IntervalMulBody.source_mul code lib.mul lib.addU lib.mulU lib.ceilDiv lib.arithmeticParameters
            maxCtx scaleCtx al ah bl bh domain.1 domain.2
        | divI=>
          exact IntervalDivBody.source_divI code lib.divI lib.addU lib.mulU lib.ceilDiv lib.arithmeticParameters
            maxCtx scaleCtx al ah bl bh domain.1 domain.2.1 domain.2.2.1 domain.2.2.2
        | positiveSub=>
          exact raise_once (raise_once (PositiveSubBody.source_positiveSub code lib.positiveSub s al ah bl bh))
  · contradiction

end SynergyC.ComputableIntervalBinary
