/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SignedAddShape

namespace ScopedC.SignedAddCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.NatWrapperCalls
open ScopedC.DyadicRepresentation
open ScopedC.SignedPairFrames (frame)
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def resultSign (a b : Endpoint) : Nat := if magnitude a b==0 then 0 else SignedNegCalls.bit (negative a b)
def result (s : State) (a b : Endpoint) : Value := SignedValues.value s.nats.values.length (resultSign a b)
def saResult (l : PoolCalls.PoolLayout) (s : State) (cells : List (Option Value)) (top high : Nat)
    (a b : Endpoint) : State := SignedCalls.siResult l s cells top high (magnitude a b)

/-- All three actual signed-add branches, including the readonly nle call,
selected na/ns body and real smake zero normalization. -/
theorem sa_closed (code : List Function) (installed : Generated.f_sa∈code)
    (naInstalled : Generated.f_na∈code) (nsInstalled : Generated.f_ns∈code)
    (nleInstalled : Generated.f_nle∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (a b : Endpoint) (aLive : a.Live s) (bLive : b.Live s)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top+1<PoolCalls.capacity) :
    SourceCall Header.layout code 5 "sa" [a.source,b.source] s (result s a b)
      (saResult l s cells top high a b) := by
  let mid := binaryResult l s cells top high (magnitude a b)
  let cells1 := cells.set top (some (.natObject s.nats.values.length))
  let final := saResult l s cells top high a b
  let before := frame s a b
  let afterArith := frame mid a b
  let after := frame final a b
  let slot := s.nats.values.length
  let sign := SignedNegCalls.bit (negative a b)
  have room0 : top<PoolCalls.capacity := by omega
  have c1 : PoolCalls.GenericPoolContext l mid cells1 (top+1) (max high (top+1)) :=
    binary_result_context context room0
  have ctxBefore : PoolCalls.GenericPoolContext l before cells top high := TwoFrames.context_frame context _ _ _ _ _ _
  have ctxMiddle : PoolCalls.GenericPoolContext l afterArith cells1 (top+1) (max high (top+1)) :=
    TwoFrames.context_frame c1 _ _ _ _ _ _
  have cmpProof : SourceCall Header.layout code 1 "nle" [.natObject b.slot,.natObject a.slot]
      before (unsigned32 (SignedNegCalls.bit (left a b))) before := by
    have h := HelperCodeAdapters.nle_for_code code nleInstalled (s:=before) bLive aLive
    by_cases hl : b.magnitude≤a.magnitude <;>
      simpa [left,hl,PrimitiveCalls.u32,unsigned32,SignedNegCalls.bit] using h
  have arithProof : SourceCall Header.layout code 2 (opName a b)
      [.natObject (firstSlot a b),.natObject (secondSlot a b)] before (.natObject slot) afterArith := by
    cases hs : same a b with
    | true =>
      have h := na_call code naInstalled keepInstalled ctxBefore room0 aLive bLive
      simpa only [opName,firstSlot,secondSlot,magnitude,hs,↓reduceIte,
        before,afterArith,slot,mid,frame,SignedPairFrames.frame,binary_result_two_frame context,
        SignedMultiplyCalls.two_frame_nats] using h
    | false =>
      cases hl : left a b with
      | true =>
        have h := ns_call code nsInstalled keepInstalled ctxBefore room0 aLive bLive
        simpa only [opName,firstSlot,secondSlot,magnitude,hs,hl,Bool.false_eq_true,↓reduceIte,
          before,afterArith,slot,mid,frame,SignedPairFrames.frame,binary_result_two_frame context,
          SignedMultiplyCalls.two_frame_nats] using h
      | false =>
        have h := ns_call code nsInstalled keepInstalled ctxBefore room0 bLive aLive
        simpa only [opName,firstSlot,secondSlot,magnitude,hs,hl,Bool.false_eq_true,↓reduceIte,
          before,afterArith,slot,mid,frame,SignedPairFrames.frame,binary_result_two_frame context,
          SignedMultiplyCalls.two_frame_nats] using h
  have magLive : NatArena.Borrow mid.nats slot (magnitude a b) := binary_result_borrow l s cells top high _
  have makeProof : SourceCall Header.layout code 4 "smake" [.natObject slot,unsigned32 sign]
      afterArith (result s a b) after := by
    have h := SignedCalls.smake_call (input:=unsigned32 sign) code smakeInstalled nzInstalled nuInstalled
      neInstalled keepInstalled ctxMiddle room magLive (SignedNegCalls.bit_bound _)
      (RationalUnsignedCalls.cast_parameter
        (allocate {afterArith with env:=[]} "N" "mag" (some (.natObject slot))) sign (SignedNegCalls.bit_bound _))
    simpa only [afterArith,after,frame,SignedPairFrames.frame,final,saResult,SignedCalls.siResult,
      result,resultSign,slot,sign,mid,cells1,binary_result_two_frame c1] using h
  let cmpEvent : CallEvents.Event Header.layout code 4 :=
    ⟨"nle",[.natObject b.slot,.natObject a.slot],before,unsigned32 (SignedNegCalls.bit (left a b)),before,
      raise_once (raise_once (raise_once cmpProof))⟩
  let arithEvent : CallEvents.Event Header.layout code 4 :=
    ⟨opName a b,[.natObject (firstSlot a b),.natObject (secondSlot a b)],before,.natObject slot,afterArith,
      raise_once (raise_once arithProof)⟩
  let makeEvent : CallEvents.Event Header.layout code 4 :=
    ⟨"smake",[.natObject slot,unsigned32 sign],afterArith,result s a b,after,makeProof⟩
  let service := CallEvents.append (CallEvents.one cmpEvent)
    (CallEvents.append (CallEvents.one arithEvent) (CallEvents.one makeEvent))
  have cmpAnswer : service "nle" [.natObject b.slot,.natObject a.slot] before=
      some (unsigned32 (SignedNegCalls.bit (left a b)),before) := CallEvents.append_left (CallEvents.one_self cmpEvent)
  have arithName : opName a b≠"nle" := by unfold opName; split <;> decide
  have makeName : "smake"≠opName a b := by unfold opName; split <;> decide
  have arithAnswer : service (opName a b) [.natObject (firstSlot a b),.natObject (secondSlot a b)] before=
      some (.natObject slot,afterArith) :=
    CallEvents.append_right (CallEvents.one_other cmpEvent arithName _ _)
      (CallEvents.append_left (CallEvents.one_self arithEvent))
  have makeAnswer : service "smake" [.natObject slot,unsigned32 sign] afterArith=some (result s a b,after) :=
    CallEvents.append_right (CallEvents.one_other cmpEvent (by change ("smake":String)≠"nle"; decide +kernel) _ _)
      (CallEvents.append_right (CallEvents.one_other arithEvent makeName _ _) (CallEvents.one_self makeEvent))
  have less : Eval Header.layout service lessTest before before (unsigned32 (SignedNegCalls.bit (left a b))) :=
    ⟨5,ExpressionTemplates.call_two Header.layout service
      (SignedPairFrames.eval_b_mag service 2 s a b) (SignedPairFrames.eval_a_mag service 2 s a b) cmpAnswer⟩
  have expr : evalExpr Header.layout service 6 before (selectedReturn a b)=some (result s a b,after) := by
    have arith := arithAnswer
    have make := makeAnswer
    cases hs : same a b with
    | true =>
      simp only [opName,firstSlot,secondSlot,sign,negative,hs,↓reduceIte] at arith make
      simpa only [selectedReturn,hs,↓reduceIte,plusReturn] using
        (ExpressionTemplates.call_two Header.layout service
          (ExpressionTemplates.call_two Header.layout service (SignedPairFrames.eval_a_mag service 2 s a b)
            (SignedPairFrames.eval_b_mag service 2 s a b) arith)
          (SignedPairFrames.eval_a_neg service 3 mid a b) make)
    | false =>
      cases hl : left a b with
      | true =>
        simp only [opName,firstSlot,secondSlot,sign,negative,hs,hl,Bool.false_eq_true,↓reduceIte] at arith make
        simpa only [selectedReturn,hs,hl,Bool.false_eq_true,↓reduceIte,leftReturn] using
          (ExpressionTemplates.call_two Header.layout service
            (ExpressionTemplates.call_two Header.layout service (SignedPairFrames.eval_a_mag service 2 s a b)
              (SignedPairFrames.eval_b_mag service 2 s a b) arith)
            (SignedPairFrames.eval_a_neg service 3 mid a b) make)
      | false =>
        simp only [opName,firstSlot,secondSlot,sign,negative,hs,hl,Bool.false_eq_true,↓reduceIte] at arith make
        simpa only [selectedReturn,hs,hl,Bool.false_eq_true,↓reduceIte,rightReturn] using
          (ExpressionTemplates.call_two Header.layout service
            (ExpressionTemplates.call_two Header.layout service (SignedPairFrames.eval_b_mag service 2 s a b)
              (SignedPairFrames.eval_a_mag service 2 s a b) arith)
            (SignedPairFrames.eval_b_neg service 3 mid a b) make)
  have shape : final.heap.length=s.heap.length ∧ final.env=s.env := RationalUnsignedCalls.si_shape l s cells top high _
  have paramLength : after.heap.length=before.heap.length := by
    simpa only [after,before,frame,SignedPairFrames.frame,TwoFrames.frame,allocate,
      List.length_append,List.length_singleton] using congrArg (fun n => n+1+1) shape.1
  have paramEnv : after.env=before.env := by
    simp only [after,before,frame,SignedPairFrames.frame,TwoFrames.frame,allocate,
      List.length_append,List.length_singleton,shape.1]
  have sourceBody := body service s after a b (result s a b) paramLength paramEnv less ⟨6,expr⟩
  have outputLive : NatArena.Borrow after.nats slot (magnitude a b) := RationalUnsignedCalls.si_borrow l s cells top high _
  have bound : resultSign a b<2^32 := by unfold resultSign; split; decide; exact SignedNegCalls.bit_bound _
  apply installed_body (f:=Generated.f_sa) (rank:=4) (service:=service) installed
    (fun _ _ _ _ _ h => CallEvents.append_closed (fun _ _ _ _ _ h => CallEvents.one_closed cmpEvent h)
      (fun _ _ _ _ _ h => CallEvents.append_closed (fun _ _ _ _ _ h => CallEvents.one_closed arithEvent h)
        (fun _ _ _ _ _ h => CallEvents.one_closed makeEvent h) h) h)
    (SignedPairFrames.bind a b aLive bLive) sourceBody
  exact ⟨SignedValues.cast_record "static S" (by decide +kernel) outputLive bound,
    (TwoFrames.pop_frame "S" "a" a.source "S" "b" b.source shape.1 shape.2).symm⟩

end ScopedC.SignedAddCalls
