/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceCalls

namespace ScopedC.TypedFrames
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

 def setObject (s : State) (i : Nat) (o : Object) : State := {s with heap:=s.heap.set i o}

 theorem bind_one (cfg : Layout) (s : State) (type name : String) (arg value : Value)
    (cast : castValue cfg {s with env:=[]} 100 type arg = some value) :
    bindArgs cfg [(type,name)] [arg] s =
      some (allocate {s with env:=[]} type name (some value)) := by
  simp [bindArgs,List.foldlM,cast]

 theorem bind_two (cfg : Layout) (s : State) (ta na tb nb : String) (a b va vb : Value)
    (ca : castValue cfg {s with env:=[]} 100 ta a = some va)
    (cb : castValue cfg (allocate {s with env:=[]} ta na (some va)) 100 tb b = some vb) :
    bindArgs cfg [(ta,na),(tb,nb)] [a,b] s =
      some (allocate (allocate {s with env:=[]} ta na (some va)) tb nb (some vb)) := by
  simp [bindArgs,List.foldlM,ca,cb]

 theorem allocate_getVar (s : State) (type name : String) (value : Option Value) :
    getVar (allocate s type name value) name = some ⟨s.heap.length,0,[]⟩ := by
  simp [getVar,allocate]

 theorem allocate_heap (s : State) (type name : String) (value : Option Value) :
    (allocate s type name value).heap[s.heap.length]? = some {type:=type,cells:=[value]} := by
  simp [allocate]

 theorem allocate_read (cfg : Layout) (s : State) (type name : String) (value : Value)
    (init : initialized 1000 value = true) :
    read cfg (allocate s type name (some value)) ⟨s.heap.length,0,[]⟩ = some value := by
  simp [Machine.read,allocate_heap,nested,init]

 theorem allocate_eval (cfg : Layout) (call : Call) (fuel : Nat) (s : State) (type name : String) (value : Value)
    (init : initialized 1000 value = true)
    (h0 : name ≠ "true") (h1 : name ≠ "false") (h2 : name ≠ "nullptr") (h3 : name ≠ "NULL") :
    evalExpr cfg call (fuel+1) (allocate s type name (some value)) (.var name) =
      some (value,allocate s type name (some value)) := by
  rw [evalExpr]
  simp [h0,h1,h2,h3,allocate_getVar,allocate_heap,allocate_read cfg s type name value init]

 theorem allocate_setObject (s : State) (i : Nat) (o : Object) (type name : String) (value : Option Value)
    (hi : i < s.heap.length) :
    allocate (setObject s i o) type name value = setObject (allocate s type name value) i o := by
  simp [allocate,setObject,List.set_append_left i o hi]

 theorem pop_allocate (s : State) (type name : String) (value : Option Value) :
    popScope s (allocate s type name value) = s := by simp [popScope,allocate]


end ScopedC.TypedFrames
