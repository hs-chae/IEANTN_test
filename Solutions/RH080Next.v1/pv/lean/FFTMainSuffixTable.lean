/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixRoot
import FFTTwiddleSource
import FFTMainLocalsTransport
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

def tableOldVar : TwiddleSource.InitVar→FullVar
  | .n=>some (.inl none)
  | .twiddle=>some (.inl (some .twiddle))
  | .root=>some (.inr .root)
  | .work=>some (.inl (some .work))
  | .status=>none

theorem tableOldVar_injective : Function.Injective tableOldVar := by
  intro a b same
  cases a <;> cases b <;> simp_all [tableOldVar]

def tableOldIds (nId : Nat) (ids : Role→Nat) (pointerBase status : Nat) : TwiddleSource.InitVar→Nat:=
  fun v=>fullIds nId ids pointerBase status (tableOldVar v)

theorem ready_table_parameters {F : Type} {state : State F} {n nId owner pointerBase status : Nat}
    {objects ids : Role→Nat} {workData : Nat→Nat}
    (h : Ready state n nId owner objects ids pointerBase status workData) :
    Locals state (fun v=>TwiddleSource.name (TwiddleSource.lift v))
      (fun v=>TwiddleSource.type (TwiddleSource.lift v)) (tableOldIds nId ids pointerBase status) state.scope
      (fun v=>TwiddleSource.values (objects .twiddle) (objects .work) n 0 (TwiddleSource.lift v)) := by
  rw [h.scope]
  refine ⟨?_,?_,h.locals.distinct.comp tableOldVar_injective,h.locals.bound⟩
  · intro v;have hv:=h.locals.lookup (tableOldVar v);cases v <;> exact hv
  · intro v;have hv:=h.locals.slots (tableOldVar v);cases v <;> exact hv

/-- An object frame preserves an already established typed host array outside
its true write set, even when temporary source declarations advance clocks. -/
theorem array_after_frame {F : Type} {before after : State F} {object size cutoff : Nat}
    {data : Nat→Nat} {writes : List Nat} (well : WellScoped before)
    (rep : WordArrayRep before object size data) (old : object<cutoff)
    (frame : Frame cutoff before after writes) (outside : object∉writes) :
    WordArrayRep after object size data :=
  ⟨frame.mode.trans rep.1,(frame.outside object old outside).trans rep.2.1,rep.2.2⟩

/-- The actual source twiddle constructor starts at the actual root-ready
main state and preserves the still-zero input/output arrays and accumulators. -/
theorem ready_construct_table {F : Type} (context : Context F)
    (pinned : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program)
    {before : State F} {n nId owner pointerBase status : Nat} {objects ids : Role→Nat} {workData : Nat→Nat}
    (h : Ready before n nId owner objects ids pointerBase status workData) (grid : RootSource.OriginalGrid n) :
    ∃after jId tableData finalWork,
      NormalSegment context before [TwiddleSource.unitAssignment,TwiddleSource.jDeclaration,TwiddleSource.loop] after ∧
      TwiddleSource.View after (objects .twiddle) (objects .work) n
        (TwiddleSource.combinedIds (tableOldIds nId ids pointerBase status) jId) before.scope (n/2)
        tableData finalWork (FFT.IntegerModel.root n) ∧
      FullMainLocals after n nId owner objects ids pointerBase status ∧
      WordArrayRep after (objects .data) (n*12) (fun _=>0) ∧
      WordArrayRep after (objects .output) (n*12) (fun _=>0) ∧
      (∀k,k<512 → 46≤k → finalWork k=workData k) ∧
      Frame before.nextObject before after [objects .twiddle,objects .work] := by
  have different : objects .twiddle≠objects .work := by intro same;have bad:=h.distinct same;cases bad
  have digits : ∀c : Fin 2,∀d,d<5→workData (128+6*c.val+d)<1000000000 := by
    intro c d hd
    fin_cases c
    · simpa [IncrementSource.base] using h.rootReal.digits d hd
    · simpa [IncrementSource.base] using h.rootImag.digits d hd
  have signs : ∀c : Fin 2,workData (128+6*c.val+5)≤1 := by
    intro c;fin_cases c
    · simpa using h.rootReal.sign
    · simpa using h.rootImag.sign
  obtain ⟨_,_,_,_,_,_,after,jId,tableData,finalWork,run,view,frame,unchanged,every⟩:=
    TwiddleSource.source_construct_table context pinned before (objects .twiddle) (objects .work) n
      (tableOldIds nId ids pointerBase status) workData grid h.well (ready_table_parameters h)
      (h.arrays .twiddle) (h.arrays .work) different digits signs h.rootValue
  have untouched (r : Role) (nr : r≠.twiddle) (nw : r≠.work) :
      WordArrayRep after (objects r) (length n r) (data workData r) := by
    apply array_after_frame h.well (h.arrays r) (h.well.objectIds _ _ (h.arrays r).2.1) frame
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
    exact ⟨fun same=>nr (h.distinct same),fun same=>nw (h.distinct same)⟩
  have fullLocals:=MainTransport.full_main_after_table h.locals h.well (h.arrays .twiddle) (h.arrays .work) frame run
  exact ⟨after,jId,tableData,finalWork,⟨run,every⟩,view,fullLocals,
    untouched .data (by decide) (by decide),untouched .output (by decide) (by decide),unchanged,frame⟩

#print axioms ready_table_parameters
#print axioms array_after_frame
#print axioms ready_construct_table
end RH080Next.FFTPV.MainSuffix
