/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SignedPairFrames
import ScopedC.RationalUnsignedCall
import ScopedC.NatWrapperCalls

namespace ScopedC.SignedMultiplyCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.NatWrapperCalls
open ScopedC.DyadicRepresentation
open ScopedC.SignedPairFrames (frame)
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def resultSign (a b : Endpoint) : Nat :=
  if a.magnitude*b.magnitude==0 then 0 else SignedNegCalls.bit (a.negative != b.negative)

def result (s : State) (a b : Endpoint) : Value := SignedValues.value s.nats.values.length (resultSign a b)

def smResult (l : PoolCalls.PoolLayout) (s : State) (cells : List (Option Value)) (top high : Nat)
    (a b : Endpoint) : State := SignedCalls.siResult l s cells top high (a.magnitude*b.magnitude)

def flagExpr : Expr := .binary "%"
  (.binary "+" (.field "." (.var "a") "neg") (.field "." (.var "b") "neg")) (.nat 2)

theorem frame_nats (s : State) (a b : Endpoint) : (frame s a b).nats=s.nats := rfl

theorem two_frame_nats (s : State) (ta na : String) (va : Value) (tb nb : String) (vb : Value) :
    (TwoFrames.frame s ta na va tb nb vb).nats=s.nats := rfl

theorem flags_add (s : State) (a b : Bool) :
    binaryValue Header.layout s "+" (unsigned32 (SignedNegCalls.bit a)) (unsigned32 (SignedNegCalls.bit b))=
      some (unsigned32 (SignedNegCalls.bit a+SignedNegCalls.bit b)) := by
  cases a <;> cases b <;> rfl

theorem flags_mod (s : State) (a b : Bool) :
    binaryValue Header.layout s "%" (unsigned32 (SignedNegCalls.bit a+SignedNegCalls.bit b))
      (.integer ⟨⟨true,32⟩,2⟩)=some (unsigned32 (SignedNegCalls.bit (a != b))) := by
  cases a <;> cases b <;> rfl

theorem flag_expression (call : Call) (s : State) (a b : Endpoint) :
    evalExpr Header.layout call 5 (frame s a b) flagExpr=
      some (unsigned32 (SignedNegCalls.bit (a.negative != b.negative)),frame s a b) := by
  have add : evalExpr Header.layout call 4 (frame s a b)
      (.binary "+" (.field "." (.var "a") "neg") (.field "." (.var "b") "neg"))=
      some (unsigned32 (SignedNegCalls.bit a.negative+SignedNegCalls.bit b.negative),frame s a b) := by
    exact ExpressionTemplates.binary Header.layout call (by decide) (by decide) (by decide) (by decide)
      (SignedPairFrames.eval_a_neg call 1 s a b) (SignedPairFrames.eval_b_neg call 1 s a b)
      (flags_add (frame s a b) _ _)
  exact ExpressionTemplates.binary Header.layout call (by decide) (by decide) (by decide) (by decide)
    add (by rfl) (flags_mod (frame s a b) _ _)

/-- Actual signed multiplication: the real nm body produces a fresh product
Nat, the exact source flag circuit computes xor, and real smake normalizes zero. -/
theorem sm_closed (code : List Function) (installed : Generated.f_sm∈code)
    (nmInstalled : Generated.f_nm∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (a b : Endpoint) (aLive : a.Live s) (bLive : b.Live s)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top+1<PoolCalls.capacity) :
    SourceCall Header.layout code 5 "sm" [a.source,b.source] s (result s a b)
      (smResult l s cells top high a b) := by
  let product := a.magnitude*b.magnitude
  let middle := binaryResult l s cells top high product
  let cells1 := cells.set top (some (.natObject s.nats.values.length))
  let final := smResult l s cells top high a b
  let before := frame s a b
  let afterNm := frame middle a b
  let after := frame final a b
  let slot := s.nats.values.length
  let sign := SignedNegCalls.bit (a.negative != b.negative)
  have room0 : top<PoolCalls.capacity := by omega
  have c1 : PoolCalls.GenericPoolContext l middle cells1 (top+1) (max high (top+1)) :=
    binary_result_context context room0
  have contextBefore : PoolCalls.GenericPoolContext l before cells top high :=
    TwoFrames.context_frame context _ _ _ _ _ _
  have contextMiddle : PoolCalls.GenericPoolContext l afterNm cells1 (top+1) (max high (top+1)) :=
    TwoFrames.context_frame c1 _ _ _ _ _ _
  have nmProof : SourceCall Header.layout code 2 "nm" [.natObject a.slot,.natObject b.slot]
      before (.natObject slot) afterNm := by
    have h := nm_call code nmInstalled keepInstalled contextBefore room0 aLive bLive
    simpa only [before,afterNm,frame,SignedPairFrames.frame,middle,product,slot,
      binary_result_two_frame context,two_frame_nats] using h
  have productLive : NatArena.Borrow middle.nats slot product := binary_result_borrow l s cells top high product
  have makeProof : SourceCall Header.layout code 4 "smake" [.natObject slot,unsigned32 sign]
      afterNm (result s a b) after := by
    have h := SignedCalls.smake_call (input:=unsigned32 sign) code smakeInstalled nzInstalled nuInstalled
      neInstalled keepInstalled contextMiddle room productLive (SignedNegCalls.bit_bound _)
      (RationalUnsignedCalls.cast_parameter
        (allocate {afterNm with env:=[]} "N" "mag" (some (.natObject slot))) sign (SignedNegCalls.bit_bound _))
    simpa only [afterNm,after,frame,SignedPairFrames.frame,final,smResult,SignedCalls.siResult,
      result,resultSign,product,slot,sign,middle,cells1,binary_result_two_frame c1] using h
  let nmEvent : CallEvents.Event Header.layout code 4 :=
    ⟨"nm",[.natObject a.slot,.natObject b.slot],before,.natObject slot,afterNm,
      raise_once (raise_once nmProof)⟩
  let makeEvent : CallEvents.Event Header.layout code 4 :=
    ⟨"smake",[.natObject slot,unsigned32 sign],afterNm,result s a b,after,makeProof⟩
  let service := CallEvents.append (CallEvents.one nmEvent) (CallEvents.one makeEvent)
  have nmAnswer : service "nm" [.natObject a.slot,.natObject b.slot] before=some (.natObject slot,afterNm) :=
    CallEvents.append_left (CallEvents.one_self nmEvent)
  have makeAnswer : service "smake" [.natObject slot,unsigned32 sign] afterNm=some (result s a b,after) :=
    CallEvents.append_right (CallEvents.one_other nmEvent
      (by change ("smake":String)≠"nm"; decide +kernel) _ _) (CallEvents.one_self makeEvent)
  have expr : evalExpr Header.layout service 6 before
      (.call (.var "smake") [.call (.var "nm") [.field "." (.var "a") "mag",.field "." (.var "b") "mag"],
        flagExpr])=some (result s a b,after) :=
    ExpressionTemplates.call_two Header.layout service
      (ExpressionTemplates.call_two Header.layout service (SignedPairFrames.eval_a_mag service 2 s a b)
        (SignedPairFrames.eval_b_mag service 2 s a b) nmAnswer)
      (flag_expression service middle a b) makeAnswer
  have shape : final.heap.length=s.heap.length ∧ final.env=s.env :=
    RationalUnsignedCalls.si_shape l s cells top high product
  have paramLength : after.heap.length=before.heap.length := by
    simpa only [after,before,frame,SignedPairFrames.frame,TwoFrames.frame,allocate,
      List.length_append,List.length_singleton] using congrArg (fun n => n+1+1) shape.1
  have paramEnv : after.env=before.env := by
    simp only [after,before,frame,SignedPairFrames.frame,TwoFrames.frame,allocate,List.length_append,List.length_singleton,shape.1]
  have body : Run Header.layout service Generated.f_sm.body before (.returned after (result s a b)) := by
    apply Loops.StmtRun.sequence (Loops.SeqRun.returned (Loops.StmtRun.returnValue ⟨6,expr⟩))
    exact ⟨rfl,(PoolCalls.pop_same paramLength paramEnv).symm⟩
  have outputLive : NatArena.Borrow after.nats slot product := RationalUnsignedCalls.si_borrow l s cells top high product
  have signBound : resultSign a b<2^32 := by
    unfold resultSign
    split
    · decide
    · exact SignedNegCalls.bit_bound _
  apply installed_body (f:=Generated.f_sm) (rank:=4) (service:=service) installed
    (fun _ _ _ _ _ h => CallEvents.append_closed
      (fun _ _ _ _ _ h => CallEvents.one_closed nmEvent h)
      (fun _ _ _ _ _ h => CallEvents.one_closed makeEvent h) h)
    (SignedPairFrames.bind a b aLive bLive) body
  exact ⟨SignedValues.cast_record "static S" (by decide +kernel) outputLive signBound,
    (TwoFrames.pop_frame "S" "a" a.source "S" "b" b.source shape.1 shape.2).symm⟩

end ScopedC.SignedMultiplyCalls
