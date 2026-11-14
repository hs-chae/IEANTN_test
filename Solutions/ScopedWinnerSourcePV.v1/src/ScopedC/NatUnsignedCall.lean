/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.OneFrames
import ScopedC.NatWrapperTemplate

namespace ScopedC.NatWrapperCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def unsigned32 (n : Nat) : Value := .integer ⟨⟨false,32⟩,(n:Int)⟩

theorem unsigned_runtime {s : State} {n : Nat} (bound : n < 2^32) :
    RuntimeCore.call "lean_unsigned_to_nat" [unsigned32 n] s =
      some (.natObject s.nats.values.length,{s with nats:=(NatArena.allocate s.nats n).2}) := by
  have nonneg : (0:Int) ≤ n := by omega
  have upper : (n:Int) < 2^32 := by exact_mod_cast bound
  simp [RuntimeCore.call,RuntimeCore.binaryName,unsigned32,nonneg,upper,RuntimeCore.result,
    NatArena.allocate]
  exact bound

theorem nu_call (code : List Function) (installed : Generated.f_nu ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)} {top high n : Nat} {input : Value}
    (context : GenericPoolContext l s cells top high) (room : top < capacity)
    (bound : n < 2^32)
    (parameter : castValue Header.layout {s with env:=[]} 100 "unsigned int" input = some (unsigned32 n)) :
    SourceCall Header.layout code 2 "nu" [input] s
      (.natObject s.nats.values.length) (binaryResult l s cells top high n) := by
  let slot := s.nats.values.length
  let fresh : State := {s with nats:=(NatArena.allocate s.nats n).2}
  let frame := OneFrames.frame s "unsigned int" "a" (unsigned32 n)
  let after := OneFrames.frame fresh "unsigned int" "a" (unsigned32 n)
  let final := keepResult l after cells top high slot
  let service := PoolModel.runtimeKeep l
  have freshContext : GenericPoolContext l fresh cells top high := context_nats context _
  have afterContext : GenericPoolContext l after cells top high :=
    OneFrames.context_frame freshContext _ _ _
  have live : NatArena.Borrow after.nats slot n := NatArena.allocate_borrow s.nats n
  have primitive : service "lean_unsigned_to_nat" [unsigned32 n] frame = some (.natObject slot,after) := by
    apply PoolModel.runtimeKeep_primitive
    simpa only [frame,after,fresh,slot,OneFrames.frame,allocate] using
      unsigned_runtime (s:=frame) bound
  have keep : service "keep" [.natObject slot] after = some (.natObject slot,final) :=
    PoolModel.runtimeKeep_keep afterContext room live
  have expression : Eval Header.layout service
      (.call (.var "keep") [.call (.var "lean_unsigned_to_nat") [.var "a"]]) frame final (.natObject slot) := by
    refine ⟨5,?_⟩
    apply ExpressionTemplates.call_one Header.layout service
      (ExpressionTemplates.call_one Header.layout service
        (TypedFrames.allocate_eval Header.layout service 2 {s with env:=[]} "unsigned int" "a"
          (unsigned32 n) rfl (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel)) primitive) keep
  have statement : Run Header.layout service Generated.f_nu.body frame (.returned final (.natObject slot)) := by
    apply Loops.StmtRun.sequence (Loops.SeqRun.returned (Loops.StmtRun.returnValue expression))
    exact ⟨rfl,(pop_same (keep_result_shape l after cells top high slot).1
      (keep_result_shape l after cells top high slot).2.1).symm⟩
  apply installed_body (rank:=1) (service:=service) installed
    (fun _ _ _ _ _ h => PoolModel.runtimeKeep_closed code keepInstalled l h)
    (TypedFrames.bind_one Header.layout s "unsigned int" "a" input (unsigned32 n) parameter) statement
  change castValue Header.layout final 100 "static N" (.natObject slot) = some (.natObject slot) ∧
    binaryResult l s cells top high n = popScope s final
  constructor
  · change castValue Header.layout final 100 "N" (.natObject slot) = some (.natObject slot)
    apply PrimitiveCalls.cast_N (n:=n)
    simpa only [final,keep_result_nats] using live
  · have normalized : final = OneFrames.frame (binaryResult l s cells top high n)
        "unsigned int" "a" (unsigned32 n) := by
      exact OneFrames.result_frame freshContext _ _ _
    rw [normalized]
    apply Eq.symm
    apply OneFrames.pop_frame
    · exact (keep_result_shape l fresh cells top high slot).1
    · exact (keep_result_shape l fresh cells top high slot).2.1

end ScopedC.NatWrapperCalls
