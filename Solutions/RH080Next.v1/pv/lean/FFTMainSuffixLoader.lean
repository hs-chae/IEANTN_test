/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixLoaderBindings
import FFTMainSuffixScopes
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

def loaderStatements (p : InputLoader.Profile) : List Stmt:=[MainCounters.reset "j",InputLoader.loop p.count]

theorem actual_w4_loader : ((bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 20).take 2=loaderStatements .w4 := by rfl
theorem actual_fap_loader : ((bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 20).take 2=loaderStatements .fap := by rfl

/-- Actual source j reset and complete source input construction, consuming
only genuine table-ready main bindings and the actual still-zero input buffer. -/
theorem load_input {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) {before : State F}
    {nId owner pointerBase status jId : Nat} {objects ids : Role→Nat} {tableData workData : Nat→Nat}
    (full : FullMainLocals before p.grid nId owner objects ids pointerBase status)
    (view : TwiddleSource.View before (objects .twiddle) (objects .work) p.grid
      (TwiddleSource.combinedIds (tableOldIds nId ids pointerBase status) jId) owner (p.grid/2)
      tableData workData (FFT.IntegerModel.root p.grid))
    (dataZero : WordArrayRep before (objects .data) (p.grid*12) (fun _=>0))
    (outputZero : WordArrayRep before (objects .output) (p.grid*12) (fun _=>0))
    (distinct : Function.Injective objects) (scope : before.scope=owner) :
    ∃after,
      NormalSegment context before (loaderStatements p) after ∧
      FullMainLocals after p.grid nId owner objects ids pointerBase status ∧
      Locals after InputLoader.parameterName InputLoader.parameterType (loaderIds nId ids jId) owner
        (InputLoader.parameterValues ⟨p,objects .data⟩ p.count) ∧
      WordArrayRep after (objects .data) (p.grid*12) (InputLoader.currentData p.encoded p.grid p.count) ∧
      WordArrayRep after (objects .output) (p.grid*12) (fun _=>0) ∧
      WordArrayRep after (objects .twiddle) (p.grid/2*12) tableData ∧
      WordArrayRep after (objects .work) 512 workData ∧
      (∀k,k<p.grid→ComplexSource.pair (InputLoader.currentData p.encoded p.grid p.count) (12*k)=p.mathematicalInput k) ∧
      after.scope=owner ∧ WellScoped after := by
  have differentJ:=full_main_j_distinct full view
  have jLookup : before.environment.lookup "j"=some (scalarPointer jId .u64):=view.locals.lookup .j
  have jSlot : Slot before jId owner .u64 (.integer (integer64 (p.grid/2))):=view.locals.slots .j
  obtain ⟨resetAfter,resetRun,jZero,resetFrame,resetEnv⟩:=
    MainCounters.reset_execution context before "j" jId owner _ view.well jLookup jSlot
  have resetLocals : FullMainLocals resetAfter p.grid nId owner objects ids pointerBase status := by
    apply MainTransport.locals_of_frame view.well full resetFrame (fun v=>by rw [resetEnv])
    intro v;simpa using differentJ v
  have resetArray {object size : Nat} {data : Nat→Nat} (rep : WordArrayRep before object size data) :
      WordArrayRep resetAfter object size data := by
    apply MainTransport.array_of_frame view.well rep resetFrame
    simpa using MultiplyParameters.array_slot_different rep jSlot
  have inputArray : WordArrayRep resetAfter (objects .data) (12*p.grid) (fun _=>0):=by
    simpa only [Nat.mul_comm] using resetArray dataZero
  have resetLookup : resetAfter.environment.lookup "j"=some (scalarPointer jId .u64):=by rw [resetEnv];exact jLookup
  have params:=loader_parameters resetLocals resetLookup jZero (differentJ (some (.inl none)))
  have separation : ∀v,objects .data≠loaderIds nId ids jId v:=by
    intro v;exact MultiplyParameters.array_slot_different inputArray (params.slots v)
  obtain ⟨after,loaded,every,array,parameters,frame,values⟩:=
    InputLoader.input_loader_total context resetAfter ⟨p,objects .data⟩ owner (loaderIds nId ids jId)
      pinned resetFrame.well inputArray params separation
  have loopSegment : NormalSegment context resetAfter [InputLoader.loop p.count] after:=
    .single loaded (by intro other flow actual;exact every other flow actual)
  have fullAfter : FullMainLocals after p.grid nId owner objects ids pointerBase status:=by
    apply MainTransport.locals_of_frame resetFrame.well resetLocals frame.frame (fun v=>by rw [frame.environment])
    intro v
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
    exact ⟨(MultiplyParameters.array_slot_different inputArray (resetLocals.slots v)).symm,differentJ v⟩
  have otherArray {r : Role} {size : Nat} {data : Nat→Nat}
      (rep : WordArrayRep before (objects r) size data) (nr : r≠.data) :
      WordArrayRep after (objects r) size data:=by
    have current:=resetArray rep
    apply MainTransport.array_of_frame resetFrame.well current frame.frame
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
    exact ⟨fun same=>nr (distinct same),MultiplyParameters.array_slot_different rep jSlot⟩
  have resetScope : resetAfter.scope=before.scope:=by
    have e:=resetRun.execution
    cases e with
    | abrupt h no=>exact False.elim (no rfl)
    | cons h rest=>cases rest;exact pure_assignment_scope (by trivial) (by trivial) h
  exact ⟨after,resetRun.append loopSegment,fullAfter,parameters,
    by simpa only [Nat.mul_comm] using array,otherArray outputZero (by decide),
    otherArray view.table (by decide),otherArray view.work (by decide),values,
    frame.scope.trans (resetScope.trans scope),frame.frame.well⟩

#print axioms actual_w4_loader
#print axioms actual_fap_loader
#print axioms load_input
end RH080Next.FFTPV.MainSuffix
