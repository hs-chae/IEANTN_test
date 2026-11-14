/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NatUnsignedCall
import ScopedC.CallEvents

namespace ScopedC.NatWrapperCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem nz_call (code : List Function) (installed : Generated.f_nz ∈ code)
    (nuInstalled : Generated.f_nu ∈ code) (neInstalled : Generated.f_ne ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)} {top high a n : Nat}
    (context : GenericPoolContext l s cells top high) (room : top < capacity)
    (ha : NatArena.Borrow s.nats a n) :
    SourceCall Header.layout code 3 "nz" [.natObject a] s
      (PrimitiveCalls.u32 (n==0)) (binaryResult l s cells top high 0) := by
  let frame := OneFrames.frame s "N" "a" (.natObject a)
  let after := binaryResult l frame cells top high 0
  let slot := s.nats.values.length
  have frameContext : GenericPoolContext l frame cells top high := OneFrames.context_frame context _ _ _
  have hnats : after.nats = (NatArena.allocate s.nats 0).2 := by
    dsimp only [after,binaryResult]
    rw [keep_result_nats]
    rfl
  have oldLive : NatArena.Borrow after.nats a n := by
    have index : a < s.nats.values.length := (List.getElem?_eq_some_iff.mp ha.1).choose
    rw [hnats]
    constructor
    · simpa only [NatArena.allocate,List.getElem?_append_left index] using ha.1
    · simpa only [NatArena.allocate,if_neg (Nat.ne_of_lt index)] using ha.2
  have zeroLive : NatArena.Borrow after.nats slot 0 := by
    rw [hnats]
    exact NatArena.allocate_borrow s.nats 0
  let nuEvent : CallEvents.Event Header.layout code 2 :=
    ⟨"nu",[.integer ⟨⟨true,32⟩,0⟩],frame,.natObject slot,after,
      nu_call code nuInstalled keepInstalled frameContext room (by decide) rfl⟩
  let neEvent : CallEvents.Event Header.layout code 2 :=
    ⟨"ne",[.natObject a,.natObject slot],after,PrimitiveCalls.u32 (n==0),after,
      raise_once (HelperCodeAdapters.ne_for_code code neInstalled oldLive zeroLive)⟩
  let service := CallEvents.append (CallEvents.one nuEvent) (CallEvents.one neEvent)
  have hnu : service "nu" [.integer ⟨⟨true,32⟩,0⟩] frame = some (.natObject slot,after) :=
    CallEvents.append_left (CallEvents.one_self nuEvent)
  have hne : service "ne" [.natObject a,.natObject slot] after =
      some (PrimitiveCalls.u32 (n==0),after) :=
    CallEvents.append_right (CallEvents.one_other nuEvent (by change ("ne":String) ≠ "nu"; decide +kernel) _ _)
      (CallEvents.one_self neEvent)
  have va : evalExpr Header.layout service 4 frame (.var "a") = some (.natObject a,frame) :=
    TypedFrames.allocate_eval Header.layout service 3 {s with env:=[]} "N" "a" (.natObject a)
      rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have vz : evalExpr Header.layout service 3 frame (.nat 0) =
      some (.integer ⟨⟨true,32⟩,0⟩,frame) := rfl
  have expression : Eval Header.layout service
      (.call (.var "ne") [.var "a",.call (.var "nu") [.nat 0]])
      frame after (PrimitiveCalls.u32 (n==0)) := by
    exact ⟨5,ExpressionTemplates.call_two Header.layout service va
      (ExpressionTemplates.call_one Header.layout service vz hnu) hne⟩
  have shape : after.heap.length = frame.heap.length ∧ after.env = frame.env :=
    ⟨(keep_result_shape l {frame with nats:=(NatArena.allocate frame.nats 0).2}
      cells top high frame.nats.values.length).1,
      (keep_result_shape l {frame with nats:=(NatArena.allocate frame.nats 0).2}
      cells top high frame.nats.values.length).2.1⟩
  have statement : Run Header.layout service Generated.f_nz.body frame
      (.returned after (PrimitiveCalls.u32 (n==0))) := by
    apply Loops.StmtRun.sequence (Loops.SeqRun.returned (Loops.StmtRun.returnValue expression))
    exact ⟨rfl,(pop_same shape.1 shape.2).symm⟩
  apply installed_body (rank:=2) (service:=service) installed
    (fun _ _ _ _ _ h => CallEvents.append_closed
      (fun _ _ _ _ _ hc => CallEvents.one_closed nuEvent hc)
      (fun _ _ _ _ _ hc => CallEvents.one_closed neEvent hc) h)
    (TypedFrames.bind_one Header.layout s "N" "a" (.natObject a) (.natObject a)
      (PrimitiveCalls.cast_N ha)) statement
  change castValue Header.layout after 100 "static unsigned int" (PrimitiveCalls.u32 (n==0)) =
      some (PrimitiveCalls.u32 (n==0)) ∧ binaryResult l s cells top high 0 = popScope s after
  constructor
  · exact PrimitiveCalls.cast32 after (n==0)
  · have normalized : after = OneFrames.frame (binaryResult l s cells top high 0) "N" "a" (.natObject a) := by
      exact OneFrames.result_frame (context_nats context (NatArena.allocate s.nats 0).2) _ _ _
    rw [normalized]
    apply Eq.symm
    apply OneFrames.pop_frame
    · exact (keep_result_shape l {s with nats:=(NatArena.allocate s.nats 0).2}
        cells top high slot).1
    · exact (keep_result_shape l {s with nats:=(NatArena.allocate s.nats 0).2}
        cells top high slot).2.1

end ScopedC.NatWrapperCalls
