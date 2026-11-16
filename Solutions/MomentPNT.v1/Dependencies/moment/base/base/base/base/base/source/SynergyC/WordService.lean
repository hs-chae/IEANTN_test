/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.AddBody
import SynergyC.MulBody
import SynergyC.IntervalValues
import ScopedC.SourceCallRanks

namespace SynergyC.WordService
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def emptyEnvContext {s : State} (ctx : MaxContext s) : MaxContext {s with env:=[]} := {
  address:=ctx.address,located:=ctx.located,allocated:=ctx.allocated,object:=ctx.object,
  heap_entry:=ctx.heap_entry,scalar:=ctx.scalar,contents:=ctx.contents}

def allocateContext {s : State} (ctx : MaxContext s) (ty name : String) (v : Option Value) :
    MaxContext (allocate s ty name v) := {
  address:=ctx.address
  located:=ctx.located
  allocated:=by simpa [allocate] using Nat.lt.step ctx.allocated
  object:=ctx.object
  heap_entry:=by simpa only [allocate,List.getElem?_append_left ctx.allocated] using ctx.heap_entry
  scalar:=ctx.scalar
  contents:=by rw [WordFrames.read_append _ _ _ _ _ _ ctx.allocated]; exact ctx.contents}

def intervalFrameContext {s : State} (ctx : MaxContext s) (al ah bl bh : Int) :
    MaxContext (IntervalValues.frame s al ah bl bh) :=
  allocateContext (allocateContext (emptyEnvContext ctx) "I" "a"
    (some (ZeroBody.interval al ah))) "I" "b" (some (ZeroBody.interval bl bh))

noncomputable section

/-- Proof-only call composition. This is not a runtime or expected-output
primitive: every successful branch is proved below by the actual installed
C function body. The heap precondition is ordinary initialized MAXU storage. -/
def add : Call := fun name args s => by
  classical
  exact if name = "addU" then
    match args with
    | [.integer a,.integer b] =>
      if a.type = type ∧ b.type = type ∧ Range a.number ∧ Range b.number ∧
          Range (a.number+b.number) ∧ Nonempty (MaxContext s) then
        some (value (a.number+b.number),s)
      else none
    | _ => none
  else none

theorem add_complete {s : State} (ctx : MaxContext s) {a b : Int}
    (ha : Range a) (hb : Range b) (hab : Range (a+b)) :
    add "addU" [value a,value b] s = some (value (a+b),s) := by
  classical
  simp [add,value,word,ha,hb,hab,Nonempty.intro ctx]

theorem add_closed (code : List Function) (installed : Generated.f_addU ∈ code)
    {name : String} {args : List Value} {s t : State} {v : Value}
    (h : add name args s = some (v,t)) :
    SourceCall Header.layout code 1 name args s v t := by
  classical
  unfold add at h
  split_ifs at h with hn
  · subst name
    split at h
    · rename_i a b
      split_ifs at h with guard
      · rcases guard with ⟨ha,hb,hra,hrb,hrab,⟨ctx⟩⟩
        have hva : Value.integer a = value a.number := by
          cases a with
          | mk ty n => change Value.integer ⟨ty,n⟩ = value n; cases ha; rfl
        have hvb : Value.integer b = value b.number := by
          cases b with
          | mk ty n => change Value.integer ⟨ty,n⟩ = value n; cases hb; rfl
        cases h
        rw [hva,hvb]
        exact AddBody.source_addU code installed ctx hra hrb hrab
    · contradiction

end
end SynergyC.WordService
