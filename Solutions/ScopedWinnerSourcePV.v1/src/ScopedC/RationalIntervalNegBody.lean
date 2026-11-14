/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.RationalInputs
import ScopedC.IntervalCasts
import ScopedC.NatResultFrames

namespace ScopedC.RationalIntervalNegCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.NatWrapperCalls
open ScopedC.RationalInputs
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def value (lo hi : Data) : Value := IntervalCasts.value lo.source hi.source

def result (lo hi : Data) : Value := IntervalCasts.value hi.negatedSource lo.negatedSource

def frame (s : State) (lo hi : Data) : State := OneFrames.frame s "RI" "a" (value lo hi)

def rnegResult (l : PoolCalls.PoolLayout) (s : State) (cells : List (Option Value)) (top high : Nat) : State :=
  binaryResult l (binaryResult l s cells top high 0)
    (cells.set top (some (.natObject s.nats.values.length))) (top+1) (max high (top+1)) 0

def initializer : Expr := .record [
  .call (.var "qn") [.field "." (.var "a") "hi"],
  .call (.var "qn") [.field "." (.var "a") "lo"]]

theorem frame_nats (s : State) (lo hi : Data) : (frame s lo hi).nats=s.nats := rfl

theorem eval_var (call : Call) (fuel : Nat) (s : State) (lo hi : Data) :
    evalExpr Header.layout call (fuel+1) (frame s lo hi) (.var "a")=some (value lo hi,frame s lo hi) :=
  TypedFrames.allocate_eval Header.layout call fuel {s with env:=[]} "RI" "a" (value lo hi)
    (by rfl) (by decide) (by decide) (by decide) (by decide)

theorem eval_lo (call : Call) (fuel : Nat) (s : State) (lo hi : Data) :
    evalExpr Header.layout call (fuel+2) (frame s lo hi) (.field "." (.var "a") "lo")=
      some (lo.source,frame s lo hi) := by
  apply ExpressionTemplates.field Header.layout call (eval_var call fuel s lo hi)
  rfl

theorem eval_hi (call : Call) (fuel : Nat) (s : State) (lo hi : Data) :
    evalExpr Header.layout call (fuel+2) (frame s lo hi) (.field "." (.var "a") "hi")=
      some (hi.source,frame s lo hi) := by
  apply ExpressionTemplates.field Header.layout call (eval_var call fuel s lo hi)
  rfl

/-- The original rneg body really calls qn twice, updates the owned pool twice,
and swaps the two resulting endpoints. No assumed callback answer is used. -/
theorem rneg_closed (code : List Function) (installed : Generated.f_rneg∈code)
    (qnInstalled : Generated.f_qn∈code) (snInstalled : Generated.f_sn∈code)
    (smakeInstalled : Generated.f_smake∈code) (nzInstalled : Generated.f_nz∈code)
    (nuInstalled : Generated.f_nu∈code) (neInstalled : Generated.f_ne∈code)
    (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (lo hi : Data) (loLive : lo.Live s) (hiLive : hi.Live s)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top+1<PoolCalls.capacity) :
    SourceCall Header.layout code 7 "rneg" [value lo hi] s (result lo hi)
      (rnegResult l s cells top high) := by
  let middle := binaryResult l s cells top high 0
  let cells1 := cells.set top (some (.natObject s.nats.values.length))
  let final := rnegResult l s cells top high
  let before := frame s lo hi
  let afterFirst := frame middle lo hi
  let after := frame final lo hi
  have room0 : top<PoolCalls.capacity := by omega
  have c1 : PoolCalls.GenericPoolContext l middle cells1 (top+1) (max high (top+1)) :=
    binary_result_context context room0
  have ctxBefore : PoolCalls.GenericPoolContext l before cells top high :=
    OneFrames.context_frame context _ _ _
  have ctxMiddle : PoolCalls.GenericPoolContext l afterFirst cells1 (top+1) (max high (top+1)) :=
    OneFrames.context_frame c1 _ _ _
  have loMid : lo.Live middle := Data.live_after loLive
  have firstProof : SourceCall Header.layout code 6 "qn" [hi.source] before hi.negatedSource afterFirst := by
    have h := RationalNegCalls.qn_closed code qnInstalled snInstalled smakeInstalled nzInstalled nuInstalled
      neInstalled keepInstalled hi.negative ctxBefore room0 hiLive.1 hiLive.2
    simpa only [before,afterFirst,frame,Data.source,Data.negatedSource,Data.negativeWord,
      middle,binary_result_one_frame context,RecordCasts.rational,RationalNegCalls.value,
      SignedValues.value,SignedNegCalls.value] using h
  have secondProof : SourceCall Header.layout code 6 "qn" [lo.source] afterFirst lo.negatedSource after := by
    have h := RationalNegCalls.qn_closed code qnInstalled snInstalled smakeInstalled nzInstalled nuInstalled
      neInstalled keepInstalled lo.negative ctxMiddle room loMid.1 loMid.2
    simpa only [afterFirst,after,frame,Data.source,Data.negatedSource,Data.negativeWord,
      final,rnegResult,middle,cells1,binary_result_one_frame c1,RecordCasts.rational,RationalNegCalls.value,
      SignedValues.value,SignedNegCalls.value] using h
  let firstEvent : CallEvents.Event Header.layout code 6 :=
    ⟨"qn",[hi.source],before,hi.negatedSource,afterFirst,firstProof⟩
  let secondEvent : CallEvents.Event Header.layout code 6 :=
    ⟨"qn",[lo.source],afterFirst,lo.negatedSource,after,secondProof⟩
  let service := CallEvents.append (CallEvents.one firstEvent) (CallEvents.one secondEvent)
  have firstAnswer : service "qn" [hi.source] before=some (hi.negatedSource,afterFirst) :=
    CallEvents.append_left (CallEvents.one_self firstEvent)
  have lengthStep : middle.nats.values.length=s.nats.values.length+1 := by
    simp only [middle,binary_result_nats,NatArena.allocate,List.length_append,List.length_singleton]
  have different : afterFirst≠before := by
    intro eq
    have lengths := congrArg (fun st : State => st.nats.values.length) eq
    simp only [afterFirst,before,frame_nats] at lengths
    omega
  have noFirst : CallEvents.one firstEvent "qn" [lo.source] afterFirst=none := by
    simp [CallEvents.one,firstEvent,different]
  have secondAnswer : service "qn" [lo.source] afterFirst=some (lo.negatedSource,after) :=
    CallEvents.append_right noFirst (CallEvents.one_self secondEvent)
  have expr : evalExpr Header.layout service 1000 before initializer=
      some (.aggregate [hi.negatedSource,lo.negatedSource],after) :=
    ExpressionTemplates.record_two Header.layout service
      (ExpressionTemplates.call_one Header.layout service (eval_hi service 996 s lo hi) firstAnswer)
      (ExpressionTemplates.call_one Header.layout service (eval_lo service 996 middle lo hi) secondAnswer)
  have loFinal : lo.Live final := Data.live_after loMid
  have hiFinal : hi.Live final := Data.live_after (Data.live_after hiLive)
  have childLo : castValue Header.layout after 99 "Q" lo.negatedSource=some lo.negatedSource :=
    Data.cast_negative 96 "Q" (by decide +kernel) loFinal
  have childHi : castValue Header.layout after 99 "Q" hi.negatedSource=some hi.negatedSource :=
    Data.cast_negative 96 "Q" (by decide +kernel) hiFinal
  have aggregate : castValue Header.layout after 100 "RI"
      (.aggregate [hi.negatedSource,lo.negatedSource])=some (result lo hi) :=
    IntervalCasts.aggregate after 96 _ _ childHi childLo
  have shape1 := SignedNegCalls.result_shape l s cells top high
  have shape2 := SignedNegCalls.result_shape l middle cells1 (top+1) (max high (top+1))
  have finalShape : final.heap.length=s.heap.length ∧ final.env=s.env :=
    ⟨shape2.1.trans shape1.1,shape2.2.trans shape1.2⟩
  have length : after.heap.length=before.heap.length := by
    simpa only [after,before,frame,OneFrames.frame,allocate,List.length_append,List.length_singleton]
      using congrArg (fun x => x+1) finalShape.1
  have environment : after.env=before.env := by
    simp only [after,before,frame,OneFrames.frame,allocate,finalShape.1]
  have body := DeclarationReturn.body Header.layout service "RI" "r" initializer expr aggregate (by rfl)
    (by decide) (by decide) (by decide) (by decide)
  rw [LocalScope.pop_local "RI" "r" (result lo hi) length environment] at body
  have paramLo : castValue Header.layout {s with env:=[]} 99 "Q" lo.source=some lo.source :=
    Data.cast 96 "Q" (by decide +kernel) loLive
  have paramHi : castValue Header.layout {s with env:=[]} 99 "Q" hi.source=some hi.source :=
    Data.cast 96 "Q" (by decide +kernel) hiLive
  apply installed_body (f:=Generated.f_rneg) (rank:=6) (service:=service) installed
    (fun _ _ _ _ _ hc => CallEvents.append_closed
      (fun _ _ _ _ _ h => CallEvents.one_closed firstEvent h)
      (fun _ _ _ _ _ h => CallEvents.one_closed secondEvent h) hc)
    (TypedFrames.bind_one Header.layout s "RI" "a" (value lo hi) (value lo hi)
      (IntervalCasts.record {s with env:=[]} 96 "RI" (by decide +kernel) _ _ paramLo paramHi)) body
  exact ⟨IntervalCasts.record after 96 "static RI" (by decide +kernel) _ _ childHi childLo,
    (OneFrames.pop_frame "RI" "a" (value lo hi) finalShape.1 finalShape.2).symm⟩

end ScopedC.RationalIntervalNegCalls
