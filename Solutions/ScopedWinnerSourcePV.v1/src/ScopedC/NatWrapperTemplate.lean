/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NatFrames

namespace ScopedC.NatWrapperCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The exact post-state of one borrowed binary Nat primitive followed by the
 application's actual keep body. Heap output is derived from the body stores. -/
def binaryResult (l : PoolLayout) (s : State) (cells : List (Option Value))
    (top high result : Nat) : State :=
  keepResult l {s with nats:=(NatArena.allocate s.nats result).2}
    cells top high s.nats.values.length

/-- An actual AST template, not a whole-function name rule. Every successful
 subcall is a generic runtime primitive or an already proved keep body. -/
theorem binary_call (code : List Function) (f : Function) (runtime : String)
    (op : NatArena.BinaryOp) (installed : f ∈ code) (keepInstalled : Generated.f_keep ∈ code)
    (parameters : f.parameters = [("N","a"),("N","b")])
    (returns : f.returnType = "static N")
    (body : f.body = .sequence [.returnStmt (.call (.var "keep")
      [.call (.var runtime) [.var "a",.var "b"]])])
    (runtimeName : RuntimeCore.binaryName runtime = some op)
    {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high a b n m result : Nat}
    (context : GenericPoolContext l s cells top high) (room : top < capacity)
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m)
    (operation : NatArena.operation op n m = some result) :
    SourceCall Header.layout code 2 f.name [.natObject a,.natObject b] s
      (.natObject s.nats.values.length) (binaryResult l s cells top high result) := by
  let slot := s.nats.values.length
  let fresh : State := {s with nats:=(NatArena.allocate s.nats result).2}
  let frame := PrimitiveCalls.frame s a b
  let after := PrimitiveCalls.frame fresh a b
  let final := keepResult l after cells top high slot
  let service := PoolModel.runtimeKeep l
  have freshContext : GenericPoolContext l fresh cells top high := context_nats context _
  have afterContext : GenericPoolContext l after cells top high := NatFrames.context_frame freshContext a b
  have live : NatArena.Borrow after.nats slot result := NatArena.allocate_borrow s.nats result
  have primitive : service runtime [.natObject a,.natObject b] frame = some (.natObject slot,after) := by
    apply PoolModel.runtimeKeep_primitive
    simpa only [frame,after,fresh,slot,PrimitiveCalls.frame,allocate] using
      NatFrames.runtime_binary (s:=frame) runtimeName ha hb operation
  have keep : service "keep" [.natObject slot] after = some (.natObject slot,final) :=
    PoolModel.runtimeKeep_keep afterContext room live
  have expression : Eval Header.layout service
      (.call (.var "keep") [.call (.var runtime) [.var "a",.var "b"]]) frame final (.natObject slot) := by
    refine ⟨5,?_⟩
    apply ExpressionTemplates.call_one Header.layout service
      (ExpressionTemplates.call_two Header.layout service
        (PrimitiveCalls.eval_var_a service 2 s a b)
        (PrimitiveCalls.eval_var_b service 2 s a b) primitive) keep
  have statement : Run Header.layout service f.body frame (.returned final (.natObject slot)) := by
    rw [body]
    apply Loops.StmtRun.sequence (Loops.SeqRun.returned (Loops.StmtRun.returnValue expression))
    exact ⟨rfl,(pop_same (keep_result_shape l after cells top high slot).1
      (keep_result_shape l after cells top high slot).2.1).symm⟩
  apply installed_body (rank:=1) (service:=service) installed
    (fun _ _ _ _ _ h => PoolModel.runtimeKeep_closed code keepInstalled l h)
    (by simpa only [parameters] using PrimitiveCalls.frame_bind ha hb) statement
  change castValue Header.layout final 100 f.returnType (.natObject slot) = some (.natObject slot) ∧
    binaryResult l s cells top high result = popScope s final
  constructor
  · rw [returns]
    change castValue Header.layout final 100 "N" (.natObject slot) = some (.natObject slot)
    apply PrimitiveCalls.cast_N (n:=result)
    simpa only [final,keep_result_nats] using live
  · have normalized : final = PrimitiveCalls.frame (binaryResult l s cells top high result) a b := by
      exact NatFrames.result_frame freshContext
    rw [normalized]
    apply Eq.symm
    apply NatFrames.pop_frame
    · exact (keep_result_shape l fresh cells top high slot).1
    · exact (keep_result_shape l fresh cells top high slot).2.1

end ScopedC.NatWrapperCalls
