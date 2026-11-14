/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.DyadicRepresentation
import ScopedC.NatResultFrames

namespace ScopedC.DyadicIntervalNegCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.NatWrapperCalls
open ScopedC.DyadicRepresentation
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def value (lo hi : Endpoint) (ok : Bool) : Value := DyadicCasts.value lo.source hi.source ok

def result (lo hi : Endpoint) (ok : Bool) : Value := DyadicCasts.value hi.negativeSource lo.negativeSource ok

def frame (s : State) (lo hi : Endpoint) (ok : Bool) : State := OneFrames.frame s "I" "a" (value lo hi ok)

def inegResult (l : PoolCalls.PoolLayout) (s : State) (cells : List (Option Value)) (top high : Nat) : State :=
  binaryResult l (binaryResult l s cells top high 0)
    (cells.set top (some (.natObject s.nats.values.length))) (top+1) (max high (top+1)) 0

def initializer : Expr := .record [
  .call (.var "sn") [.field "." (.var "a") "hi"],
  .call (.var "sn") [.field "." (.var "a") "lo"],
  .field "." (.var "a") "ok"]

theorem frame_nats (s : State) (lo hi : Endpoint) (ok : Bool) : (frame s lo hi ok).nats=s.nats := rfl

theorem eval_var (call : Call) (fuel : Nat) (s : State) (lo hi : Endpoint) (ok : Bool) :
    evalExpr Header.layout call (fuel+1) (frame s lo hi ok) (.var "a")=some (value lo hi ok,frame s lo hi ok) :=
  TypedFrames.allocate_eval Header.layout call fuel {s with env:=[]} "I" "a" (value lo hi ok)
    (by rfl) (by decide) (by decide) (by decide) (by decide)

theorem eval_lo (call : Call) (fuel : Nat) (s : State) (lo hi : Endpoint) (ok : Bool) :
    evalExpr Header.layout call (fuel+2) (frame s lo hi ok) (.field "." (.var "a") "lo")=
      some (lo.source,frame s lo hi ok) := by
  apply ExpressionTemplates.field Header.layout call (eval_var call fuel s lo hi ok)
  rfl

theorem eval_hi (call : Call) (fuel : Nat) (s : State) (lo hi : Endpoint) (ok : Bool) :
    evalExpr Header.layout call (fuel+2) (frame s lo hi ok) (.field "." (.var "a") "hi")=
      some (hi.source,frame s lo hi ok) := by
  apply ExpressionTemplates.field Header.layout call (eval_var call fuel s lo hi ok)
  rfl

theorem eval_ok (call : Call) (fuel : Nat) (s : State) (lo hi : Endpoint) (ok : Bool) :
    evalExpr Header.layout call (fuel+2) (frame s lo hi ok) (.field "." (.var "a") "ok")=
      some (unsigned32 (SignedNegCalls.bit ok),frame s lo hi ok) := by
  apply ExpressionTemplates.field Header.layout call (eval_var call fuel s lo hi ok)
  rfl

theorem record_three (cfg : Layout) (call : Call) {s m t u : State}
    {a b c : Expr} {x y z : Value} {fuel : Nat}
    (ha : evalExpr cfg call fuel s a=some (x,m))
    (hb : evalExpr cfg call fuel m b=some (y,t))
    (hc : evalExpr cfg call fuel t c=some (z,u)) :
    evalExpr cfg call (fuel+1) s (.record [a,b,c])=some (.aggregate [x,y,z],u) := by
  rw [evalExpr]
  simp [List.foldlM,ha,hb,hc]

/-- The original ineg body really calls sn twice, updates the owned pool twice,
and swaps the two resulting endpoints. No assumed callback answer is used. -/
theorem ineg_closed (code : List Function) (installed : Generated.f_ineg∈code)
    (snInstalled : Generated.f_sn∈code)
    (smakeInstalled : Generated.f_smake∈code) (nzInstalled : Generated.f_nz∈code)
    (nuInstalled : Generated.f_nu∈code) (neInstalled : Generated.f_ne∈code)
    (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (lo hi : Endpoint) (ok : Bool) (loLive : lo.Live s) (hiLive : hi.Live s)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top+1<PoolCalls.capacity) :
    SourceCall Header.layout code 6 "ineg" [value lo hi ok] s (result lo hi ok)
      (inegResult l s cells top high) := by
  let middle := binaryResult l s cells top high 0
  let cells1 := cells.set top (some (.natObject s.nats.values.length))
  let final := inegResult l s cells top high
  let before := frame s lo hi ok
  let afterFirst := frame middle lo hi ok
  let after := frame final lo hi ok
  have room0 : top<PoolCalls.capacity := by omega
  have c1 : PoolCalls.GenericPoolContext l middle cells1 (top+1) (max high (top+1)) :=
    binary_result_context context room0
  have ctxBefore : PoolCalls.GenericPoolContext l before cells top high :=
    OneFrames.context_frame context _ _ _
  have ctxMiddle : PoolCalls.GenericPoolContext l afterFirst cells1 (top+1) (max high (top+1)) :=
    OneFrames.context_frame c1 _ _ _
  have loMid : lo.Live middle := Endpoint.live_after loLive
  have firstProof : SourceCall Header.layout code 5 "sn" [hi.source] before hi.negativeSource afterFirst := by
    have h := SignedNegCalls.sn_closed code snInstalled smakeInstalled nzInstalled nuInstalled
      neInstalled keepInstalled hi.negative ctxBefore room0 hiLive
    simpa only [before,afterFirst,frame,Endpoint.source,Endpoint.negativeSource,Endpoint.negativeWord,
      middle,binary_result_one_frame context,SignedValues.value,SignedNegCalls.value] using h
  have secondProof : SourceCall Header.layout code 5 "sn" [lo.source] afterFirst lo.negativeSource after := by
    have h := SignedNegCalls.sn_closed code snInstalled smakeInstalled nzInstalled nuInstalled
      neInstalled keepInstalled lo.negative ctxMiddle room loMid
    simpa only [afterFirst,after,frame,Endpoint.source,Endpoint.negativeSource,Endpoint.negativeWord,
      final,inegResult,middle,cells1,binary_result_one_frame c1,SignedValues.value,SignedNegCalls.value] using h
  let firstEvent : CallEvents.Event Header.layout code 5 :=
    ⟨"sn",[hi.source],before,hi.negativeSource,afterFirst,firstProof⟩
  let secondEvent : CallEvents.Event Header.layout code 5 :=
    ⟨"sn",[lo.source],afterFirst,lo.negativeSource,after,secondProof⟩
  let service := CallEvents.append (CallEvents.one firstEvent) (CallEvents.one secondEvent)
  have firstAnswer : service "sn" [hi.source] before=some (hi.negativeSource,afterFirst) :=
    CallEvents.append_left (CallEvents.one_self firstEvent)
  have lengthStep : middle.nats.values.length=s.nats.values.length+1 := by
    simp only [middle,binary_result_nats,NatArena.allocate,List.length_append,List.length_singleton]
  have different : afterFirst≠before := by
    intro eq
    have lengths := congrArg (fun st : State => st.nats.values.length) eq
    simp only [afterFirst,before,frame_nats] at lengths
    omega
  have noFirst : CallEvents.one firstEvent "sn" [lo.source] afterFirst=none := by
    simp [CallEvents.one,firstEvent,different]
  have secondAnswer : service "sn" [lo.source] afterFirst=some (lo.negativeSource,after) :=
    CallEvents.append_right noFirst (CallEvents.one_self secondEvent)
  have expr : evalExpr Header.layout service 1000 before initializer=
      some (.aggregate [hi.negativeSource,lo.negativeSource,unsigned32 (SignedNegCalls.bit ok)],after) :=
    record_three Header.layout service
      (ExpressionTemplates.call_one Header.layout service (eval_hi service 996 s lo hi ok) firstAnswer)
      (ExpressionTemplates.call_one Header.layout service (eval_lo service 996 middle lo hi ok) secondAnswer)
      (eval_ok service 997 final lo hi ok)
  have loFinal : lo.Live final := Endpoint.live_after loMid
  have hiFinal : hi.Live final := Endpoint.live_after (Endpoint.live_after hiLive)
  have childLo : castValue Header.layout after 99 "S" lo.negativeSource=some lo.negativeSource :=
    Endpoint.cast_negative 97 "S" (by decide +kernel) loFinal
  have childHi : castValue Header.layout after 99 "S" hi.negativeSource=some hi.negativeSource :=
    Endpoint.cast_negative 97 "S" (by decide +kernel) hiFinal
  have aggregate : castValue Header.layout after 100 "I"
      (.aggregate [hi.negativeSource,lo.negativeSource,unsigned32 (SignedNegCalls.bit ok)])=some (result lo hi ok) :=
    DyadicCasts.aggregate after 97 _ _ ok childHi childLo
  have shape1 := SignedNegCalls.result_shape l s cells top high
  have shape2 := SignedNegCalls.result_shape l middle cells1 (top+1) (max high (top+1))
  have finalShape : final.heap.length=s.heap.length ∧ final.env=s.env :=
    ⟨shape2.1.trans shape1.1,shape2.2.trans shape1.2⟩
  have length : after.heap.length=before.heap.length := by
    simpa only [after,before,frame,OneFrames.frame,allocate,List.length_append,List.length_singleton]
      using congrArg (fun x => x+1) finalShape.1
  have environment : after.env=before.env := by
    simp only [after,before,frame,OneFrames.frame,allocate,finalShape.1]
  have body := DeclarationReturn.body Header.layout service "I" "r" initializer expr aggregate (by rfl)
    (by decide) (by decide) (by decide) (by decide)
  rw [LocalScope.pop_local "I" "r" (result lo hi ok) length environment] at body
  have paramLo : castValue Header.layout {s with env:=[]} 99 "S" lo.source=some lo.source :=
    Endpoint.cast 97 "S" (by decide +kernel) loLive
  have paramHi : castValue Header.layout {s with env:=[]} 99 "S" hi.source=some hi.source :=
    Endpoint.cast 97 "S" (by decide +kernel) hiLive
  apply installed_body (f:=Generated.f_ineg) (rank:=5) (service:=service) installed
    (fun _ _ _ _ _ hc => CallEvents.append_closed
      (fun _ _ _ _ _ h => CallEvents.one_closed firstEvent h)
      (fun _ _ _ _ _ h => CallEvents.one_closed secondEvent h) hc)
    (TypedFrames.bind_one Header.layout s "I" "a" (value lo hi ok) (value lo hi ok)
      (DyadicCasts.record {s with env:=[]} 97 "I" (by decide +kernel) _ _ ok paramLo paramHi)) body
  exact ⟨DyadicCasts.record after 97 "static I" (by decide +kernel) _ _ ok childHi childLo,
    (OneFrames.pop_frame "I" "a" (value lo hi ok) finalShape.1 finalShape.2).symm⟩

end ScopedC.DyadicIntervalNegCalls
