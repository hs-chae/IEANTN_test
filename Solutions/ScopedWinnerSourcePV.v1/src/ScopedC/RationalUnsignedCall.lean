/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SignedUnsignedCall
import ScopedC.RecordCasts
import ScopedC.LocalScope

namespace ScopedC.RationalUnsignedCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls ScopedC.NatWrapperCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def first (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high n : Nat) :=
  binaryResult l s cells top high n

def cells1 (s : State) (cells : List (Option Value)) (top : Nat) :=
  cells.set top (some (.natObject s.nats.values.length))
def cells2 (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high n : Nat) :=
  (cells1 s cells top).set (top+1) (some (.natObject (first l s cells top high n).nats.values.length))
def high2 (top high : Nat) := max (max high (top+1)) (top+1+1)

def qiResult (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high n : Nat) :=
  binaryResult l (SignedCalls.siResult l s cells top high n)
    (cells2 l s cells top high n) (top+1+1) (high2 top high) 1

theorem binary_shape (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high n : Nat) :
    (binaryResult l s cells top high n).heap.length=s.heap.length ∧
    (binaryResult l s cells top high n).env=s.env :=
  ⟨(keep_result_shape l {s with nats:=(NatArena.allocate s.nats n).2}
    cells top high s.nats.values.length).1,
    (keep_result_shape l {s with nats:=(NatArena.allocate s.nats n).2}
    cells top high s.nats.values.length).2.1⟩

theorem si_context {l : PoolLayout} {s : State} {cells : List (Option Value)} {top high n : Nat}
    (context : GenericPoolContext l s cells top high) (room : top+1<capacity) :
    GenericPoolContext l (SignedCalls.siResult l s cells top high n)
      (cells2 l s cells top high n) (top+1+1) (high2 top high) := by
  have room0 : top<capacity := by omega
  exact binary_result_context (binary_result_context (result:=n) context room0) room

theorem frame_nats (s : State) (type name : String) (v : Value) :
    (OneFrames.frame s type name v).nats=s.nats := rfl

theorem si_frame {l : PoolLayout} {s : State} {cells : List (Option Value)} {top high n : Nat}
    (context : GenericPoolContext l s cells top high) (room : top<capacity)
    (type name : String) (v : Value) :
    SignedCalls.siResult l (OneFrames.frame s type name v) cells top high n=
      OneFrames.frame (SignedCalls.siResult l s cells top high n) type name v := by
  have c1 := binary_result_context (result:=n) context room
  unfold SignedCalls.siResult
  rw [binary_result_one_frame context]
  simp only [frame_nats]
  exact binary_result_one_frame c1 type name v

theorem si_borrow (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high n : Nat) :
    NatArena.Borrow (SignedCalls.siResult l s cells top high n).nats s.nats.values.length n := by
  exact binary_result_preserves (binary_result_borrow l s cells top high n)

theorem si_shape (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high n : Nat) :
    (SignedCalls.siResult l s cells top high n).heap.length=s.heap.length ∧
    (SignedCalls.siResult l s cells top high n).env=s.env := by
  have h1 := binary_shape l s cells top high n
  have h2 := binary_shape l (first l s cells top high n) (cells1 s cells top)
    (top+1) (max high (top+1)) 0
  exact ⟨h2.1.trans h1.1,h2.2.trans h1.2⟩

theorem cast_parameter (s : State) (n : Nat) (bound : n<2^32) :
    castValue Header.layout s 100 "unsigned int" (unsigned32 n)=some (unsigned32 n) := by
  have range : Scalar.InRange ⟨false,32⟩ (n:Int) := by
    simp only [Scalar.InRange,Scalar.lower,Scalar.upper,Scalar.modulus,Bool.false_eq_true,↓reduceIte]
    exact ⟨by omega,by exact_mod_cast Nat.zero_le n,by exact_mod_cast bound⟩
  change (do let x ← Scalar.cast ⟨false,32⟩ ⟨⟨false,32⟩,(n:Int)⟩
             pure (Value.integer x))=some (unsigned32 n)
  simp only [Scalar.cast]
  rw [Scalar.make_exact range]
  rfl

/-- Actual qi initializer executes si then nu(1), with all three allocations,
source casts and mutable-pool/frame effects accounted for. -/
theorem qi_call (code : List Function) (installed : Generated.f_qi∈code)
    (siInstalled : Generated.f_si∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)} {top high n : Nat} {input : Value}
    (context : GenericPoolContext l s cells top high) (room : top+2<capacity) (bound : n<2^32)
    (parameter : castValue Header.layout {s with env:=[]} 100 "unsigned int" input=some (unsigned32 n)) :
    SourceCall Header.layout code 6 "qi" [input] s
      (RecordCasts.rational s.nats.values.length 0 (SignedCalls.siResult l s cells top high n).nats.values.length)
      (qiResult l s cells top high n) := by
  let frame := OneFrames.frame s "unsigned int" "n" (unsigned32 n)
  let middle := SignedCalls.siResult l s cells top high n
  let final := qiResult l s cells top high n
  let afterSi := OneFrames.frame middle "unsigned int" "n" (unsigned32 n)
  let after := OneFrames.frame final "unsigned int" "n" (unsigned32 n)
  let numerator := SignedValues.value s.nats.values.length 0
  let result := RecordCasts.rational s.nats.values.length 0 middle.nats.values.length
  let rawOne : Value := .integer ⟨⟨true,32⟩,1⟩
  have room0 : top<capacity := by omega
  have room1 : top+1<capacity := by omega
  have room2 : top+1+1<capacity := by omega
  have c2 := si_context (n:=n) context room1
  have contextFrame : GenericPoolContext l frame cells top high := OneFrames.context_frame context _ _ _
  have contextMiddle : GenericPoolContext l afterSi (cells2 l s cells top high n) (top+1+1) (high2 top high) :=
    OneFrames.context_frame c2 _ _ _
  have siProof : SourceCall Header.layout code 5 "si" [unsigned32 n] frame numerator afterSi := by
    have h := SignedCalls.si_call (input:=unsigned32 n) code siInstalled smakeInstalled nzInstalled
      nuInstalled neInstalled keepInstalled contextFrame room1 bound (cast_parameter {frame with env:=[]} n bound)
    simpa only [frame,afterSi,middle,numerator,si_frame context room0,frame_nats] using h
  have nuProof : SourceCall Header.layout code 2 "nu" [rawOne] afterSi
      (.natObject middle.nats.values.length) after := by
    have h := nu_call (input:=rawOne) (n:=1) code nuInstalled keepInstalled contextMiddle room2 (by decide) rfl
    simpa only [afterSi,after,final,qiResult,middle,binary_result_one_frame c2,frame_nats] using h
  let siEvent : CallEvents.Event Header.layout code 5 :=
    ⟨"si",[unsigned32 n],frame,numerator,afterSi,siProof⟩
  let nuEvent : CallEvents.Event Header.layout code 5 :=
    ⟨"nu",[rawOne],afterSi,.natObject middle.nats.values.length,after,
      raise_once (raise_once (raise_once nuProof))⟩
  let service := CallEvents.append (CallEvents.one siEvent) (CallEvents.one nuEvent)
  have siAnswer : service "si" [unsigned32 n] frame=some (numerator,afterSi) :=
    CallEvents.append_left (CallEvents.one_self siEvent)
  have nuAnswer : service "nu" [rawOne] afterSi=some (.natObject middle.nats.values.length,after) :=
    CallEvents.append_right (CallEvents.one_other siEvent
      (by change ("nu":String)≠"si"; decide +kernel) _ _) (CallEvents.one_self nuEvent)
  have var : evalExpr Header.layout service 998 frame (.var "n")=some (unsigned32 n,frame) :=
    TypedFrames.allocate_eval Header.layout service 997 {s with env:=[]} "unsigned int" "n"
      (unsigned32 n) rfl (by decide) (by decide) (by decide) (by decide)
  have expr : evalExpr Header.layout service 1000 frame
      (.record [.call (.var "si") [.var "n"],.call (.var "nu") [.nat 1]])=
      some (.aggregate [numerator,.natObject middle.nats.values.length],after) :=
    ExpressionTemplates.record_two Header.layout service
      (ExpressionTemplates.call_one Header.layout service var siAnswer)
      (ExpressionTemplates.call_one Header.layout service (by rfl) nuAnswer)
  have magLive : NatArena.Borrow after.nats s.nats.values.length n :=
    binary_result_preserves (si_borrow l s cells top high n)
  have denLive : NatArena.Borrow after.nats middle.nats.values.length 1 :=
    binary_result_borrow l middle (cells2 l s cells top high n) (top+1+1) (high2 top high) 1
  have shapeSi := si_shape l s cells top high n
  have shapeNu := binary_shape l middle (cells2 l s cells top high n) (top+1+1) (high2 top high) 1
  have finalShape : final.heap.length=s.heap.length ∧ final.env=s.env :=
    ⟨shapeNu.1.trans shapeSi.1,shapeNu.2.trans shapeSi.2⟩
  have h := DeclarationReturn.body Header.layout service "Q" "r" _ expr
    (RecordCasts.rational_aggregate after 97 magLive denLive (by decide +kernel)) (by rfl)
    (by decide) (by decide) (by decide) (by decide)
  have length : after.heap.length=frame.heap.length := by
    simpa only [after,frame,OneFrames.frame,allocate,List.length_append,List.length_singleton]
      using congrArg (fun x => x+1) finalShape.1
  have environment : after.env=frame.env := by simp only [after,frame,OneFrames.frame,allocate,finalShape.1]
  rw [LocalScope.pop_local "Q" "r" result length environment] at h
  apply installed_body (f:=Generated.f_qi) (rank:=5) (service:=service) installed
    (fun _ _ _ _ _ hc => CallEvents.append_closed
      (fun _ _ _ _ _ hs => CallEvents.one_closed siEvent hs)
      (fun _ _ _ _ _ hn => CallEvents.one_closed nuEvent hn) hc)
    (TypedFrames.bind_one Header.layout s "unsigned int" "n" input (unsigned32 n) parameter) h
  exact ⟨RecordCasts.rational_record after 97 "static Q" (by decide +kernel) magLive denLive (by decide +kernel),
    (OneFrames.pop_frame "unsigned int" "n" (unsigned32 n) finalShape.1 finalShape.2).symm⟩

/-- Fully discharged unsigned input ABI instance, with no cast premise. -/
theorem qi_closed (code : List Function) (installed : Generated.f_qi∈code)
    (siInstalled : Generated.f_si∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)} {top high n : Nat}
    (context : GenericPoolContext l s cells top high) (room : top+2<capacity) (bound : n<2^32) :
    SourceCall Header.layout code 6 "qi" [unsigned32 n] s
      (RecordCasts.rational s.nats.values.length 0 (SignedCalls.siResult l s cells top high n).nats.values.length)
      (qiResult l s cells top high n) :=
  qi_call code installed siInstalled smakeInstalled nzInstalled nuInstalled neInstalled keepInstalled
    context room bound (cast_parameter {s with env:=[]} n bound)

theorem qi_mag_live (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high n : Nat) :
    NatArena.Borrow (qiResult l s cells top high n).nats s.nats.values.length n :=
  binary_result_preserves (si_borrow l s cells top high n)

theorem qi_den_live (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high n : Nat) :
    NatArena.Borrow (qiResult l s cells top high n).nats
      (SignedCalls.siResult l s cells top high n).nats.values.length 1 :=
  binary_result_borrow l (SignedCalls.siResult l s cells top high n)
    (cells2 l s cells top high n) (top+1+1) (high2 top high) 1

end ScopedC.RationalUnsignedCalls
