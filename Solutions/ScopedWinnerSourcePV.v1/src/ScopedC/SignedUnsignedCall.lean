/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SignedMakeCall
import ScopedC.NatResultFrames

namespace ScopedC.SignedCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls ScopedC.NatWrapperCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def siResult (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high n : Nat) : State :=
  binaryResult l (binaryResult l s cells top high n)
    (cells.set top (some (.natObject s.nats.values.length))) (top+1) (max high (top+1)) 0

theorem si_call (code : List Function) (installed : Generated.f_si ∈ code)
    (smakeInstalled : Generated.f_smake ∈ code) (nzInstalled : Generated.f_nz ∈ code)
    (nuInstalled : Generated.f_nu ∈ code) (neInstalled : Generated.f_ne ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)} {top high n : Nat} {input : Value}
    (context : GenericPoolContext l s cells top high) (room : top+1 < capacity) (bound : n < 2^32)
    (parameter : castValue Header.layout {s with env:=[]} 100 "unsigned int" input = some (unsigned32 n)) :
    SourceCall Header.layout code 5 "si" [input] s
      (SignedValues.value s.nats.values.length 0) (siResult l s cells top high n) := by
  let frame := OneFrames.frame s "unsigned int" "n" (unsigned32 n)
  let first := binaryResult l s cells top high n
  let cells1 := cells.set top (some (.natObject s.nats.values.length))
  let top1 := top+1
  let high1 := max high (top+1)
  let final := siResult l s cells top high n
  let afterNu := OneFrames.frame first "unsigned int" "n" (unsigned32 n)
  let after := OneFrames.frame final "unsigned int" "n" (unsigned32 n)
  let slot := s.nats.values.length
  let result := SignedValues.value slot 0
  have room0 : top < capacity := by omega
  have context1 : GenericPoolContext l first cells1 top1 high1 := binary_result_context context room0
  have frameContext : GenericPoolContext l frame cells top high := OneFrames.context_frame context _ _ _
  have afterNuContext : GenericPoolContext l afterNu cells1 top1 high1 := OneFrames.context_frame context1 _ _ _
  have firstShape : first.heap.length = s.heap.length ∧ first.env = s.env :=
    ⟨(keep_result_shape l {s with nats:=(NatArena.allocate s.nats n).2} cells top high slot).1,
      (keep_result_shape l {s with nats:=(NatArena.allocate s.nats n).2} cells top high slot).2.1⟩
  have finalShape : final.heap.length = s.heap.length ∧ final.env = s.env :=
    ⟨(keep_result_shape l {first with nats:=(NatArena.allocate first.nats 0).2}
      cells1 top1 high1 first.nats.values.length).1.trans firstShape.1,
      (keep_result_shape l {first with nats:=(NatArena.allocate first.nats 0).2}
      cells1 top1 high1 first.nats.values.length).2.1.trans firstShape.2⟩
  have live1 : NatArena.Borrow afterNu.nats slot n := binary_result_borrow l s cells top high n
  have live2 : NatArena.Borrow after.nats slot n := binary_result_preserves (l:=l) (s:=first) (cells:=cells1) (top:=top1) (high:=high1) (result:=0) live1
  have nuProof : SourceCall Header.layout code 2 "nu" [unsigned32 n] frame (.natObject slot) afterNu := by
    have h := nu_call (input:=unsigned32 n) code nuInstalled keepInstalled frameContext room0 bound
      (cast_unsigned {frame with env:=[]} n bound)
    have frameNats : (OneFrames.frame s "unsigned int" "n" (unsigned32 n)).nats = s.nats := rfl
    simpa only [frame,afterNu,first,slot,binary_result_one_frame context,frameNats] using h
  have makeProof : SourceCall Header.layout code 4 "smake" [.natObject slot,.integer ⟨⟨true,32⟩,0⟩]
      afterNu result after := by
    have h := smake_call (neg:=0) (input:=.integer ⟨⟨true,32⟩,0⟩) code smakeInstalled nzInstalled nuInstalled neInstalled keepInstalled
      afterNuContext room live1 (by decide) rfl
    simpa only [afterNu,after,final,siResult,ite_self,binary_result_one_frame context1] using h
  let nuEvent : CallEvents.Event Header.layout code 4 :=
    ⟨"nu",[unsigned32 n],frame,.natObject slot,afterNu,raise_once (raise_once nuProof)⟩
  let makeEvent : CallEvents.Event Header.layout code 4 :=
    ⟨"smake",[.natObject slot,.integer ⟨⟨true,32⟩,0⟩],afterNu,result,after,makeProof⟩
  let service := CallEvents.append (CallEvents.one nuEvent) (CallEvents.one makeEvent)
  have nuAnswer : service "nu" [unsigned32 n] frame = some (.natObject slot,afterNu) :=
    CallEvents.append_left (CallEvents.one_self nuEvent)
  have makeAnswer : service "smake" [.natObject slot,.integer ⟨⟨true,32⟩,0⟩] afterNu = some (result,after) :=
    CallEvents.append_right (CallEvents.one_other nuEvent
      (by change ("smake":String) ≠ "nu"; decide +kernel) _ _) (CallEvents.one_self makeEvent)
  have vn : evalExpr Header.layout service 3 frame (.var "n") = some (unsigned32 n,frame) :=
    TypedFrames.allocate_eval Header.layout service 2 {s with env:=[]} "unsigned int" "n" (unsigned32 n)
      rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have expression : Eval Header.layout service
      (.call (.var "smake") [.call (.var "nu") [.var "n"],.nat 0]) frame after result :=
    ⟨5,ExpressionTemplates.call_two Header.layout service
      (ExpressionTemplates.call_one Header.layout service vn nuAnswer) rfl makeAnswer⟩
  have shape : after.heap.length = frame.heap.length ∧ after.env = frame.env := by
    constructor
    · simpa only [after,frame,OneFrames.frame,allocate,List.length_append,List.length_singleton]
        using congrArg (fun x => x+1) finalShape.1
    · simp only [after,frame,OneFrames.frame,allocate,finalShape.1]
  have statement : Run Header.layout service Generated.f_si.body frame (.returned after result) := by
    apply Loops.StmtRun.sequence (Loops.SeqRun.returned (Loops.StmtRun.returnValue expression))
    exact ⟨rfl,(pop_same shape.1 shape.2).symm⟩
  apply installed_body (rank:=4) (service:=service) installed
    (fun _ _ _ _ _ h => CallEvents.append_closed
      (fun _ _ _ _ _ hc => CallEvents.one_closed nuEvent hc)
      (fun _ _ _ _ _ hc => CallEvents.one_closed makeEvent hc) h)
    (TypedFrames.bind_one Header.layout s "unsigned int" "n" input (unsigned32 n) parameter) statement
  change castValue Header.layout after 100 "static S" result = some result ∧ final = popScope s after
  constructor
  · exact SignedValues.cast_record "static S" (by decide +kernel) live2 (by decide)
  · exact (OneFrames.pop_frame _ _ _ finalShape.1 finalShape.2).symm

end ScopedC.SignedCalls
