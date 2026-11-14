/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceCalls
import ScopedC.Generated
import ScopedC.Header

namespace ScopedC.PrimitiveCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def u8 (b : Bool) : Value := .integer ⟨⟨false,8⟩,if b then 1 else 0⟩
def u32 (b : Bool) : Value := .integer ⟨⟨false,32⟩,if b then 1 else 0⟩
def frame (s : State) (a b : Nat) : State :=
  allocate (allocate {s with env:=[]} "N" "a" (some (.natObject a)))
    "N" "b" (some (.natObject b))

private theorem normalize_N : normalizeType "N" = "N" := by decide +kernel
private theorem normalize_unsigned : normalizeType "unsigned int" = "unsigned int" := by decide +kernel
private theorem normalize_return : normalizeType "static unsigned int" = "unsigned int" := by decide +kernel
private theorem unsigned_lookup : Header.layout.integers.lookup "unsigned int" = some ⟨false,32⟩ := by decide +kernel

theorem pop_self (s : State) : popScope s s = s := by simp [popScope]
theorem pop_frame (s : State) (a b : Nat) : popScope s (frame s a b) = s := by
  simp [popScope,frame,allocate,List.take_append]

theorem frame_get_a (s : State) (a b : Nat) :
    getVar (frame s a b) "a" = some ⟨s.heap.length,0,[]⟩ := by
  simp [getVar,frame,allocate,List.lookup]
theorem frame_get_b (s : State) (a b : Nat) :
    getVar (frame s a b) "b" = some ⟨s.heap.length+1,0,[]⟩ := by
  simp [getVar,frame,allocate,List.lookup]

theorem frame_heap_a (s : State) (a b : Nat) :
    (frame s a b).heap[s.heap.length]? =
      some {type:="N",cells:=[some (.natObject a)]} := by
  simp [frame,allocate,List.getElem?_append]
theorem frame_heap_b (s : State) (a b : Nat) :
    (frame s a b).heap[s.heap.length+1]? =
      some {type:="N",cells:=[some (.natObject b)]} := by
  simp [frame,allocate,List.getElem?_append]

theorem frame_read_a (s : State) (a b : Nat) :
    read Header.layout (frame s a b) ⟨s.heap.length,0,[]⟩ = some (.natObject a) := by
  simp [Machine.read,frame_heap_a,nested,initialized]
theorem frame_read_b (s : State) (a b : Nat) :
    read Header.layout (frame s a b) ⟨s.heap.length+1,0,[]⟩ = some (.natObject b) := by
  simp [Machine.read,frame_heap_b,nested,initialized]

theorem cast_N {s : State} {a n : Nat} (h : NatArena.Borrow s.nats a n) :
    castValue Header.layout s 100 "N" (.natObject a) = some (.natObject a) := by
  change (do let _ ← NatArena.read s.nats a; pure (Value.natObject a)) = some (Value.natObject a)
  rw [NatArena.read_of_borrow h]
  rfl

theorem frame_bind {s : State} {a b n m : Nat}
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    bindArgs Header.layout [("N","a"),("N","b")]
      [.natObject a,.natObject b] s = some (frame s a b) := by
  let initial : State := {s with env:=[]}
  let first := allocate initial "N" "a" (some (.natObject a))
  have ca := cast_N (s:=initial) ha
  have cb := cast_N (s:=first) hb
  simpa [bindArgs,List.foldlM,frame,initial,first] using
    (show bindArgs Header.layout [("N","a"),("N","b")]
      [.natObject a,.natObject b] s = some (frame s a b) by
      simp [bindArgs,List.foldlM,ca,cb,frame,initial,first])

theorem eval_var_a (call : Call) (fuel : Nat) (s : State) (a b : Nat) :
    evalExpr Header.layout call (fuel+1) (frame s a b) (.var "a") =
      some (.natObject a,frame s a b) := by
  simp [evalExpr,frame_get_a,frame_heap_a,frame_read_a]
theorem eval_var_b (call : Call) (fuel : Nat) (s : State) (a b : Nat) :
    evalExpr Header.layout call (fuel+1) (frame s a b) (.var "b") =
      some (.natObject b,frame s a b) := by
  simp [evalExpr,frame_get_b,frame_heap_b,frame_read_b]

theorem cast8 (s : State) (b : Bool) :
    castValue Header.layout s 100 "unsigned int" (u8 b) = some (u32 b) := by
  change ((Scalar.cast ⟨false,32⟩ ⟨⟨false,8⟩,(if b then 1 else 0)⟩) >>=
    fun x => some (Value.integer x)) = some (u32 b)
  cases b <;> rfl
theorem cast32 (s : State) (b : Bool) :
    castValue Header.layout s 100 "static unsigned int" (u32 b) = some (u32 b) := by
  change ((Scalar.cast ⟨false,32⟩ ⟨⟨false,32⟩,(if b then 1 else 0)⟩) >>=
    fun x => some (Value.integer x)) = some (u32 b)
  cases b <;> rfl

theorem eq_runtime {s : State} {a b n m : Nat}
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    RuntimeCore.call "lean_nat_dec_eq" [.natObject a,.natObject b] s = some (u8 (n==m),s) := by
  have ra := NatArena.read_of_borrow ha
  have rb := NatArena.read_of_borrow hb
  by_cases h : n=m <;>
    simp [RuntimeCore.call,RuntimeCore.binaryName,ra,rb,h,RuntimeCore.unsignedResult,
      Scalar.checked,Scalar.InRange,Scalar.lower,Scalar.upper,Scalar.modulus,u8]

theorem le_runtime {s : State} {a b n m : Nat}
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    RuntimeCore.call "lean_nat_dec_le" [.natObject a,.natObject b] s = some (u8 (decide (n ≤ m)),s) := by
  have ra := NatArena.read_of_borrow ha
  have rb := NatArena.read_of_borrow hb
  by_cases h : n ≤ m <;>
    simp [RuntimeCore.call,RuntimeCore.binaryName,ra,rb,h,RuntimeCore.unsignedResult,
      Scalar.checked,Scalar.InRange,Scalar.lower,Scalar.upper,Scalar.modulus,u8]

theorem lt_runtime {s : State} {a b n m : Nat}
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    RuntimeCore.call "lean_nat_dec_lt" [.natObject a,.natObject b] s = some (u8 (decide (n < m)),s) := by
  have ra := NatArena.read_of_borrow ha
  have rb := NatArena.read_of_borrow hb
  by_cases h : n < m <;>
    simp [RuntimeCore.call,RuntimeCore.binaryName,ra,rb,h,RuntimeCore.unsignedResult,
      Scalar.checked,Scalar.InRange,Scalar.lower,Scalar.upper,Scalar.modulus,u8]

private theorem comparison_call (f : Function) (runtime : String) (result : Bool)
    (installed : f ∈ Generated.functions)
    (parameters : f.parameters = [("N","a"),("N","b")])
    (returns : f.returnType = "static unsigned int")
    (body : f.body = .sequence [.returnStmt (.cast "unsigned int"
      (.call (.var runtime) [.var "a",.var "b"]))])
    {s : State} {a b n m : Nat}
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m)
    (answer : RuntimeCore.call runtime [.natObject a,.natObject b] (frame s a b) =
      some (u8 result,frame s a b)) :
    SourceCall Header.layout Generated.functions 1 f.name
      [.natObject a,.natObject b] s (u32 result) s := by
  have expression : Eval Header.layout RuntimeCore.call
      (.cast "unsigned int" (.call (.var runtime) [.var "a",.var "b"]))
      (frame s a b) (frame s a b) (u32 result) := by
    refine ⟨8,?_⟩
    rw [evalExpr]
    have hc : evalExpr Header.layout RuntimeCore.call 7 (frame s a b)
        (.call (.var runtime) [.var "a",.var "b"]) = some (u8 result,frame s a b) := by
      rw [evalExpr]
      simp only [List.foldlM,eval_var_a,eval_var_b,Option.bind_some,
        List.nil_append,List.append_nil,answer]
      simp only [bind,Option.bind,pure,eval_var_b,List.cons_append,List.nil_append,answer]
    rw [hc]
    simp [cast8]
  have statement : Run Header.layout RuntimeCore.call f.body (frame s a b)
      (.returned (frame s a b) (u32 result)) := by
    rw [body]
    exact Loops.StmtRun.sequence
      (Loops.SeqRun.returned (Loops.StmtRun.returnValue expression)) ⟨rfl,(pop_self _).symm⟩
  refine installed_body (cfg:=Header.layout) (rank:=0) (service:=RuntimeCore.call)
    installed (fun _ _ _ _ _ h => h) ?_ statement ?_
  · simpa only [parameters] using frame_bind ha hb
  · change castValue Header.layout (frame s a b) 100 f.returnType (u32 result) =
        some (u32 result) ∧ s = popScope s (frame s a b)
    exact ⟨by simpa only [returns] using cast32 (frame s a b) result,(pop_frame s a b).symm⟩

theorem ne_call {s : State} {a b n m : Nat}
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    SourceCall Header.layout Generated.functions 1 "ne"
      [.natObject a,.natObject b] s (u32 (n==m)) s := by
  exact comparison_call Generated.f_ne "lean_nat_dec_eq" (n==m)
    (by simp [Generated.functions]) rfl rfl rfl ha hb (eq_runtime (s:=frame s a b) ha hb)

theorem nle_call {s : State} {a b n m : Nat}
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    SourceCall Header.layout Generated.functions 1 "nle"
      [.natObject a,.natObject b] s (u32 (decide (n ≤ m))) s := by
  exact comparison_call Generated.f_nle "lean_nat_dec_le" (decide (n ≤ m))
    (by simp [Generated.functions]) rfl rfl rfl ha hb (le_runtime (s:=frame s a b) ha hb)

theorem nlt_call {s : State} {a b n m : Nat}
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    SourceCall Header.layout Generated.functions 1 "nlt"
      [.natObject a,.natObject b] s (u32 (decide (n < m))) s := by
  exact comparison_call Generated.f_nlt "lean_nat_dec_lt" (decide (n < m))
    (by simp [Generated.functions]) rfl rfl rfl ha hb (lt_runtime (s:=frame s a b) ha hb)

#print axioms ne_call
#print axioms nle_call
#print axioms nlt_call
end ScopedC.PrimitiveCalls
