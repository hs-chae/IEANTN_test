/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SynergyC.WordCompare
import ScopedC.TypedFrameBasic
namespace SynergyC.WordFrames
open ScopedC ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def frame (s : State) (a b : Int) : State :=
  allocate (allocate {s with env:=[]} "U" "a" (some (value a))) "U" "b" (some (value b))

theorem read_append (cfg : Layout) (s : State) (ty name : String) (v : Option Value)
    (a : Address) (ha : a.object < s.heap.length) :
    read cfg (allocate s ty name v) a = read cfg s a := by
  simp only [Machine.read,allocate,List.getElem?_append_left ha]

theorem bind (s : State) {a b : Int} (ha : Range a) (hb : Range b) :
    bindArgs Header.layout [("U","a"),("U","b")] [value a,value b] s = some (frame s a b) :=
  TypedFrames.bind_two Header.layout s "U" "a" "U" "b" (value a) (value b) (value a) (value b)
    (cast_word _ ha) (cast_word _ hb)

theorem read_a (s : State) (a b : Int) :
    read Header.layout (frame s a b) ⟨s.heap.length,0,[]⟩ = some (value a) := by
  simp [Machine.read,frame,allocate,List.getElem?_append,nested,initialized,value]
theorem read_b (s : State) (a b : Int) :
    read Header.layout (frame s a b) ⟨s.heap.length+1,0,[]⟩ = some (value b) := by
  simp [Machine.read,frame,allocate,List.getElem?_append,nested,initialized,value]
theorem eval_a (call : Call) (fuel : Nat) (s : State) (a b : Int) :
    evalExpr Header.layout call (fuel+1) (frame s a b) (.var "a") = some (value a,frame s a b) := by
  simp [evalExpr,getVar,frame,allocate,List.lookup,List.getElem?_append,Machine.read,nested,initialized,value]
theorem eval_b (call : Call) (fuel : Nat) (s : State) (a b : Int) :
    evalExpr Header.layout call (fuel+1) (frame s a b) (.var "b") = some (value b,frame s a b) := by
  simp [evalExpr,getVar,frame,allocate,List.lookup,List.getElem?_append,Machine.read,nested,initialized,value]

/-- An explicit application-state precondition, to be established by the
source's static initialization. It is not a trusted program output. -/
structure MaxContext (s : State) where
  address : Address
  located : s.globals.lookup "MAXU" = some address
  allocated : address.object < s.heap.length
  object : Object
  heap_entry : s.heap[address.object]? = some object
  scalar : object.isArray = false
  contents : read Header.layout s address = some (value maxWord)

theorem eval_max (call : Call) (fuel : Nat) {s : State} (ctx : MaxContext s) (a b : Int) :
    evalExpr Header.layout call (fuel+1) (frame s a b) (.var "MAXU") = some (value maxWord,frame s a b) := by
  have hread : read Header.layout (frame s a b) ctx.address = some (value maxWord) := by
    rw [frame,read_append]
    · rw [read_append]
      · exact ctx.contents
      · exact ctx.allocated
    · simpa [allocate] using Nat.lt.step ctx.allocated
  rw [evalExpr]
  have hv : getVar (frame s a b) "MAXU" = some ctx.address := by
    simp [getVar,frame,allocate,List.lookup,ctx.located]
  have hget : (frame s a b).heap[ctx.address.object]? = some ctx.object := by
    simp only [frame,allocate]
    rw [List.getElem?_append_left (by simpa using Nat.lt.step ctx.allocated)]
    rw [List.getElem?_append_left ctx.allocated]
    exact ctx.heap_entry
  simp [hv,hget,ctx.scalar,hread]

theorem pop_frame (s : State) (a b : Int) : popScope s (frame s a b) = s := by
  simp [popScope,frame,allocate,List.take_append]

#print axioms bind
#print axioms eval_max
end SynergyC.WordFrames
