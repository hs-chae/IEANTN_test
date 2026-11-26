/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddSignFlip
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def fullIds (pi : PreVar → Nat) (first cmpId : Nat) : Var → Nat
  | .out=>pi .out | .a=>pi .a | .b=>pi .b | .subtract=>pi .subtract | .asign=>pi .asign | .bsign=>pi .bsign
  | .j=>first | .carry=>first+1 | .cmp=>cmpId

theorem slot_readonly {F : Type} {before after : State F} {id owner : Nat} {ctype : CType} {value : Value}
    (well : WellScoped before) (slot : Slot before id owner ctype value)
    (frame : CompareSource.ReadOnlyCallerFrame before after) : Slot after id owner ctype value :=
  ⟨slot.storable,by rw [frame.objects id (well.objectIds id _ slot.object)]; exact slot.object⟩

/-- The source cmp declaration receives the actual verified comparison call's
return, after the two real zero initializers. Its allocation identity is taken
from the returned source state; it is not guessed across nested calls. -/
theorem initialize_loop_vars {F : Type} (context : Context F)
    (selected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    {before : State F} {input : Input} {owner : Nat} {pi : PreVar → Nat}
    (h : PreView before input owner pi input.bsign) (scope : before.scope=owner) :
    ∃sj sc returned after : State F,
      before.declare .u64 "j" (some (.integer (integer64 0)))=some sj ∧
      sj.declare .u64 "carry" (some (.integer (integer64 0)))=some sc ∧
      returned.declare .u64 "cmp" (some (.integer (integer64 input.cmp)))=some after ∧
      CompareSource.ReadOnlyCallerFrame sc returned ∧
      ExecList context before [jDeclaration,carryDeclaration,cmpDeclaration] .normal after ∧
      ∀sub swap,View after input sub swap owner (fullIds pi before.nextObject returned.nextObject) 0 := by
  have zero:=ZeroFrame.u64_storable 0 (by norm_num)
  obtain ⟨sj,dj⟩:=ZeroFrame.declare_exists h.well .u64 "j" (.integer (integer64 0)) zero
  have ij:=declare_storable zero (convert64 0 (by norm_num)) dj
  have wj:=wellScoped_declare h.well dj
  have lj:=ApplicationBirthFrame.locals_declare_old h.well h.locals (by intro v; cases v <;> decide) ij
  have aj : ∀r,WordArrayRep sj (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r)):=
    fun r=>ApplicationBirthFrame.array_declare_old h.well (h.arrays r) ij
  obtain ⟨sc,dc⟩:=ZeroFrame.declare_exists wj .u64 "carry" (.integer (integer64 0)) zero
  have ic:=declare_storable zero (convert64 0 (by norm_num)) dc
  have wc:=wellScoped_declare wj dc
  have lc:=ApplicationBirthFrame.locals_declare_old wj lj (by intro v; cases v <;> decide) ic
  have ac : ∀r,WordArrayRep sc (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r)):=
    fun r=>ApplicationBirthFrame.array_declare_old wj (aj r) ic
  have jSlot:=ApplicationBirthFrame.slot_declare_old wj ij.slot ic
  obtain ⟨returned,called,leftPost,rightPost,callFrame⟩:=CompareSource.magnitude_compare_call context selected sc
    (input.layout.object .a) (input.layout.length (input.layout.object .a)) (input.layout.start .a)
    (input.layout.object .b) (input.layout.length (input.layout.object .b)) (input.layout.start .b)
    (input.old (input.layout.object .a)) (input.old (input.layout.object .b)) wc (ac .a) (ac .b)
    (by have hb:=input.layout.bound .a; omega) (by have hb:=input.layout.bound .b; omega)
  have args : Args context sc [.variable "a",.variable "b"]
      [.pointer (wordPointer (input.layout.object .a) (input.layout.start .a)),
       .pointer (wordPointer (input.layout.object .b) (input.layout.start .b))] sc := by
    apply Args.ordered (order:=[(0,.variable "a"),(1,.variable "b")])
      (evaluated:=[(0,.pointer (wordPointer (input.layout.object .a) (input.layout.start .a))),
        (1,.pointer (wordPointer (input.layout.object .b) (input.layout.start .b)))])
    · exact List.Perm.refl _
    · exact .cons (.variable (lc.lookup PreVar.a) (lc.read PreVar.a))
        (.cons (.variable (lc.lookup PreVar.b) (lc.read PreVar.b)) .nil)
    · change List.Forall₂ _ [0,1] _
      exact .cons rfl (.cons rfl .nil)
  have cmpBound : input.cmp ≤ 2:=CompareSource.compareDigits_le_two _ _ _
  have cmp64 : input.cmp < 2^64:=by omega
  have cmpStore:=ZeroFrame.u64_storable input.cmp cmp64
  obtain ⟨after,dCmp⟩:=ZeroFrame.declare_exists callFrame.well .u64 "cmp" (.integer (integer64 input.cmp)) cmpStore
  have im:=declare_storable cmpStore (convert64 input.cmp cmp64) dCmp
  have scopeC : sc.scope=owner:=ic.scope.trans (ij.scope.trans scope)
  have scopeR : returned.scope=owner:=callFrame.scope.trans scopeC
  have lr : Locals returned preName preType pi owner (preValues input input.bsign) := by
    refine ⟨?_,fun v=>slot_readonly wc (lc.slots v) callFrame,lc.distinct,?_⟩
    · rw [callFrame.environment]
      exact lc.lookup
    · rw [←scopeR]
      exact callFrame.well.current
  have ar : ∀r,WordArrayRep returned (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r)):=by
    intro r
    exact ⟨leftPost.1,by rw [callFrame.objects _ (wc.objectIds _ _ (ac r).2.1)]; exact (ac r).2.1,(ac r).2.2⟩
  have ja:=slot_readonly wc jSlot callFrame
  have ca:=slot_readonly wc ic.slot callFrame
  have la:=ApplicationBirthFrame.locals_declare_old callFrame.well lr (by intro v; cases v <;> decide) im
  have jFinal:=ApplicationBirthFrame.slot_declare_old callFrame.well ja im
  have cFinal:=ApplicationBirthFrame.slot_declare_old callFrame.well ca im
  have arrays : ∀r,WordArrayRep after (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r)):=
    fun r=>ApplicationBirthFrame.array_declare_old callFrame.well (ar r) im
  have oldBound (v : PreVar) : pi v < before.nextObject:=h.well.objectIds _ _ (h.locals.slots v).object
  have jBound : before.nextObject < returned.nextObject:=callFrame.well.objectIds _ _ ja.object
  have cBound : before.nextObject+1 < returned.nextObject:=by
    have hb:=callFrame.well.objectIds _ _ ca.object
    simpa only [ij.nextObject] using hb
  have oldOut:=oldBound .out
  have oldA:=oldBound .a
  have oldB:=oldBound .b
  have oldSub:=oldBound .subtract
  have oldAs:=oldBound .asign
  have oldBs:=oldBound .bsign
  have lm : Locals after name type (fullIds pi before.nextObject returned.nextObject) owner (values input 0 0):=by
    constructor
    · intro v
      cases v with
      | out=>
        simpa only [fullIds,name,type,preName,preType] using la.lookup PreVar.out
      | a=>
        simpa only [fullIds,name,type,preName,preType] using la.lookup PreVar.a
      | b=>
        simpa only [fullIds,name,type,preName,preType] using la.lookup PreVar.b
      | subtract=>
        simpa only [fullIds,name,type,preName,preType] using la.lookup PreVar.subtract
      | asign=>
        simpa only [fullIds,name,type,preName,preType] using la.lookup PreVar.asign
      | bsign=>
        simpa only [fullIds,name,type,preName,preType] using la.lookup PreVar.bsign
      | j=>
        rw [im.environment,callFrame.environment,ic.environment,ij.environment]
        simp [fullIds,name,type,preName,preType,List.lookup,scalarPointer]
      | carry=>
        rw [im.environment,callFrame.environment,ic.environment]
        simp [fullIds,name,type,preName,preType,ij.nextObject,List.lookup,scalarPointer]
      | cmp=>rw [im.environment]; rfl
    · intro v
      cases v with
      | out=>simpa only [fullIds,type,values,preType,preValues] using la.slots PreVar.out
      | a=>simpa only [fullIds,type,values,preType,preValues] using la.slots PreVar.a
      | b=>simpa only [fullIds,type,values,preType,preValues] using la.slots PreVar.b
      | subtract=>simpa only [fullIds,type,values,preType,preValues] using la.slots PreVar.subtract
      | asign=>simpa only [fullIds,type,values,preType,preValues] using la.slots PreVar.asign
      | bsign=>simpa only [fullIds,type,values,preType,preValues] using la.slots PreVar.bsign
      | j=>simpa only [fullIds,type,values,scope] using jFinal
      | carry=>simpa only [fullIds,type,values,ij.nextObject,ij.scope,scope] using cFinal
      | cmp=>simpa only [fullIds,type,values,scopeR] using im.slot
    · intro v w eq
      cases v <;> cases w <;> dsimp [fullIds] at eq ⊢
      all_goals try rfl
      all_goals try (have conflict:=h.locals.distinct eq; cases conflict)
      all_goals omega
    · rw [im.nextScope,←scopeR]
      exact callFrame.well.current
  have sep : ∀r v,input.layout.object r≠fullIds pi before.nextObject returned.nextObject v:=by
    intro r v
    have oldObject:=h.well.objectIds _ _ (h.arrays r).2.1
    cases v with
    | out=>exact h.separate r PreVar.out
    | a=>exact h.separate r PreVar.a
    | b=>exact h.separate r PreVar.b
    | subtract=>exact h.separate r PreVar.subtract
    | asign=>exact h.separate r PreVar.asign
    | bsign=>exact h.separate r PreVar.bsign
    | j=>change input.layout.object r≠before.nextObject; omega
    | carry=>change input.layout.object r≠before.nextObject+1; omega
    | cmp=>change input.layout.object r≠returned.nextObject; omega
  refine ⟨sj,sc,returned,after,dj,dc,dCmp,callFrame,
    .cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dj)
      (.cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dc)
        (.cons (.declareSome (.call args called) dCmp) .nil)),?_⟩
  intro sub swap
  refine ⟨?_,?_,sep,by norm_num,wellScoped_declare callFrame.well dCmp⟩
  · simpa only [Arrays,currentData_initial] using arrays
  · simpa only [scan_initial] using lm

#print axioms initialize_loop_vars
end RH080Next.FFTPV.AddSource
