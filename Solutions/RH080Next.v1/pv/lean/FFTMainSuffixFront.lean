/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixLoader
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

def loadedData (p : InputLoader.Profile) : Nat→Nat:=InputLoader.currentData p.encoded p.grid p.count

def frontStatements (p : InputLoader.Profile) : List Stmt:=
  rootPrefix++[TwiddleSource.unitAssignment,TwiddleSource.jDeclaration,TwiddleSource.loop]++loaderStatements p

theorem actual_w4_front : ((bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 8).take 14=frontStatements .w4 := by rfl
theorem actual_fap_front : ((bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 8).take 14=frontStatements .fap := by rfl

/-- The actual main state at instruction22. Every application representation
here is derived from the actual calloc/zero/root/table/input source sequence. -/
structure FrontReady {F : Type} (state : State F) (p : InputLoader.Profile)
    (nId owner : Nat) (objects ids : Role→Nat) (pointerBase status jId : Nat)
    (tableData workData : Nat→Nat) : Prop where
  full : FullMainLocals state p.grid nId owner objects ids pointerBase status
  loader : Locals state InputLoader.parameterName InputLoader.parameterType (loaderIds nId ids jId) owner
    (InputLoader.parameterValues ⟨p,objects .data⟩ p.count)
  dataArray : WordArrayRep state (objects .data) (p.grid*12) (loadedData p)
  output : WordArrayRep state (objects .output) (p.grid*12) (fun _=>0)
  table : WordArrayRep state (objects .twiddle) (p.grid/2*12) tableData
  work : WordArrayRep state (objects .work) 512 workData
  tableSnapshot : ∃snapshot : State F,TwiddleSource.View snapshot (objects .twiddle) (objects .work) p.grid
    (TwiddleSource.combinedIds (tableOldIds nId ids pointerBase status) jId) owner (p.grid/2)
    tableData workData (FFT.IntegerModel.root p.grid)
  inputPair : ∀k,k<p.grid→ComplexSource.pair (loadedData p) (12*k)=p.mathematicalInput k
  accumulatorsZero : ∀k,192≤k→k<214→workData k=0
  distinct : Function.Injective objects
  scope : state.scope=owner
  well : WellScoped state

/-- The first fourteen statements of the genuine nonNULL suffix execute and
uniquely establish the exact input/table state required by the actual FFT. -/
theorem raw_to_loaded {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) {before : State F} {nId owner : Nat} {objects ids : Role→Nat}
    (raw : View before p.grid nId owner [.output,.work,.twiddle,.data] objects ids) :
    ∃after pointerBase status jId tableData workData,
      NormalSegment context before (frontStatements p) after ∧
      FrontReady after p nId owner objects ids pointerBase status jId tableData workData := by
  have programs : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program:=by
    cases p with
    | fap=>exact Or.inr pinned
    | w4=>exact Or.inl pinned
  have grid : RootSource.OriginalGrid p.grid:=by cases p <;> simp [InputLoader.Profile.grid,RootSource.OriginalGrid]
  obtain ⟨rootState,pointerBase,status,rootWork,rootRun,rootReady⟩:=raw_to_root context programs raw grid
  obtain ⟨tableState,jId,tableData,workData,tableRun,tableView,full,dataZero,outputZero,workOutside,_⟩:=
    ready_construct_table context programs rootReady grid
  have tableViewOwner : TwiddleSource.View tableState (objects .twiddle) (objects .work) p.grid
      (TwiddleSource.combinedIds (tableOldIds nId ids pointerBase status) jId) owner (p.grid/2)
      tableData workData (FFT.IntegerModel.root p.grid):=by
    simpa only [rootReady.scope] using tableView
  have tableScope : tableState.scope=owner:=(table_scope tableRun.execution).trans rootReady.scope
  obtain ⟨after,loadRun,finalFull,loader,dataArray,output,table,work,inputPair,scope,well⟩:=
    load_input context p pinned full tableViewOwner dataZero outputZero rootReady.distinct tableScope
  have zeros : ∀k,192≤k→k<214→workData k=0:=by
    intro k hk hu
    rw [workOutside k (by omega) (by omega)]
    exact rootReady.workOutside k (by omega) (by omega) (by omega)
  exact ⟨after,pointerBase,status,jId,tableData,workData,(rootRun.append tableRun).append loadRun,
    ⟨finalFull,loader,dataArray,output,table,work,⟨tableState,tableViewOwner⟩,inputPair,zeros,
      rootReady.distinct,scope,well⟩⟩

#print axioms actual_w4_front
#print axioms actual_fap_front
#print axioms raw_to_loaded
end RH080Next.FFTPV.MainSuffix
