/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.DyadicRepresentation
import ScopedC.TwoFrames

namespace ScopedC.SignedPairFrames
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open ScopedC.DyadicRepresentation
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def frame (s : State) (a b : Endpoint) : State :=
  TwoFrames.frame s "S" "a" a.source "S" "b" b.source

theorem bind {s : State} (a b : Endpoint) (ha : a.Live s) (hb : b.Live s) :
    bindArgs Header.layout [("S","a"),("S","b")] [a.source,b.source] s=some (frame s a b) :=
  TypedFrames.bind_two Header.layout s "S" "a" "S" "b" a.source b.source a.source b.source
    (Endpoint.cast 98 "S" (by decide +kernel) ha)
    (Endpoint.cast 98 "S" (by decide +kernel) hb)

theorem get_a (s : State) (a b : Endpoint) :
    getVar (frame s a b) "a"=some ⟨s.heap.length,0,[]⟩ := by
  simp [getVar,frame,TwoFrames.frame,allocate,List.lookup]

theorem get_b (s : State) (a b : Endpoint) :
    getVar (frame s a b) "b"=some ⟨s.heap.length+1,0,[]⟩ := by
  simp [getVar,frame,TwoFrames.frame,allocate,List.lookup]

theorem heap_a (s : State) (a b : Endpoint) :
    (frame s a b).heap[s.heap.length]?=some {type:="S",cells:=[some a.source]} := by
  simp [frame,TwoFrames.frame,allocate,List.getElem?_append]

theorem heap_b (s : State) (a b : Endpoint) :
    (frame s a b).heap[s.heap.length+1]?=some {type:="S",cells:=[some b.source]} := by
  simp [frame,TwoFrames.frame,allocate,List.getElem?_append]

theorem read_a (s : State) (a b : Endpoint) :
    read Header.layout (frame s a b) ⟨s.heap.length,0,[]⟩=some a.source := by
  simp [Machine.read,heap_a,nested,initialized,Endpoint.source,SignedValues.value,NatWrapperCalls.unsigned32]

theorem read_b (s : State) (a b : Endpoint) :
    read Header.layout (frame s a b) ⟨s.heap.length+1,0,[]⟩=some b.source := by
  simp [Machine.read,heap_b,nested,initialized,Endpoint.source,SignedValues.value,NatWrapperCalls.unsigned32]

theorem eval_a (call : Call) (fuel : Nat) (s : State) (a b : Endpoint) :
    evalExpr Header.layout call (fuel+1) (frame s a b) (.var "a")=some (a.source,frame s a b) := by
  simp [evalExpr,get_a,heap_a,read_a]

theorem eval_b (call : Call) (fuel : Nat) (s : State) (a b : Endpoint) :
    evalExpr Header.layout call (fuel+1) (frame s a b) (.var "b")=some (b.source,frame s a b) := by
  simp [evalExpr,get_b,heap_b,read_b]

theorem eval_a_mag (call : Call) (fuel : Nat) (s : State) (a b : Endpoint) :
    evalExpr Header.layout call (fuel+2) (frame s a b) (.field "." (.var "a") "mag")=
      some (.natObject a.slot,frame s a b) := by
  apply ExpressionTemplates.field Header.layout call (eval_a call fuel s a b)
  rfl

theorem eval_b_mag (call : Call) (fuel : Nat) (s : State) (a b : Endpoint) :
    evalExpr Header.layout call (fuel+2) (frame s a b) (.field "." (.var "b") "mag")=
      some (.natObject b.slot,frame s a b) := by
  apply ExpressionTemplates.field Header.layout call (eval_b call fuel s a b)
  rfl

theorem eval_a_neg (call : Call) (fuel : Nat) (s : State) (a b : Endpoint) :
    evalExpr Header.layout call (fuel+2) (frame s a b) (.field "." (.var "a") "neg")=
      some (NatWrapperCalls.unsigned32 (SignedNegCalls.bit a.negative),frame s a b) := by
  apply ExpressionTemplates.field Header.layout call (eval_a call fuel s a b)
  rfl

theorem eval_b_neg (call : Call) (fuel : Nat) (s : State) (a b : Endpoint) :
    evalExpr Header.layout call (fuel+2) (frame s a b) (.field "." (.var "b") "neg")=
      some (NatWrapperCalls.unsigned32 (SignedNegCalls.bit b.negative),frame s a b) := by
  apply ExpressionTemplates.field Header.layout call (eval_b call fuel s a b)
  rfl

end ScopedC.SignedPairFrames
