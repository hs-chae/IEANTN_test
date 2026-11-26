/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTwiddleInitialization
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.TwiddleSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

private theorem append_normal {F : Type} {context : Context F} {before middle after : State F}
    {a b : List Stmt} {flow : Flow} (first : ExecList context before a .normal middle)
    (second : ExecList context middle b flow after) : ExecList context before (a++b) flow after := by
  induction a generalizing before with
  | nil=>cases first;exact second
  | cons x xs ih=>
    cases first with
    | cons run rest=>exact .cons run (ih rest)
    | abrupt _ bad=>exact False.elim (bad rfl)

private theorem prefix_loop_every {F : Type} {context : Context F} {before middle after other : State F} {flow : Flow}
    (setup : ExecList context before [unitAssignment,jDeclaration] .normal middle)
    (every : ∀state flow,Exec context middle loop flow state → flow=.normal ∧ state=after)
    (run : ExecList context before [unitAssignment,jDeclaration,loop] flow other) : flow=.normal ∧ other=after := by
  cases setup with
  | abrupt _ bad=>exact False.elim (bad rfl)
  | cons aRun setup=>
    cases setup with
    | abrupt _ bad=>exact False.elim (bad rfl)
    | cons bRun tail=>
      cases tail
      cases run with
      | abrupt aRun' bad=>
        have eq:=PureDeterminism.simple_unique (by simp [unitAssignment,PureDeterminism.Simple,SourcePure.CallFree]) aRun aRun'
        exact False.elim (bad eq.1.symm)
      | cons aRun' rest=>
        obtain ⟨_,eqs⟩:=PureDeterminism.simple_unique (by simp [unitAssignment,PureDeterminism.Simple,SourcePure.CallFree]) aRun aRun'
        cases eqs
        cases rest with
        | abrupt bRun' bad=>
          have eq:=PureDeterminism.simple_unique (by simp [jDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) bRun bRun'
          exact False.elim (bad eq.1.symm)
        | cons bRun' rest=>
          obtain ⟨_,eqs⟩:=PureDeterminism.simple_unique (by simp [jDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) bRun bRun'
          cases eqs
          cases rest with
          | abrupt loopRun bad=>
            have eq:=every _ _ loopRun
            exact False.elim (bad eq.1)
          | cons loopRun tail=>
            obtain ⟨_,eqs⟩:=every _ _ loopRun
            cases eqs
            cases tail
            exact ⟨rfl,rfl⟩

/-- Exact source-linked table construction for both original grids. It starts
from the real zeroed table and the independently source-verified initialized
root; all table values are consequences of actual C execution. This is a
main-program stage contract, not a complete FFT/ANT verification claim. -/
theorem construct_table {F : Type} (context : Context F) (functions : Functions context) (before : State F)
    (tableObject workObject n : Nat) (oldIds : InitVar→Nat) (workData : Nat→Nat)
    (original : n=131072 ∨ n=16777216) (well : WellScoped before)
    (locals : Locals before (fun v=>name (lift v)) (fun v=>type (lift v)) oldIds before.scope
      (fun v=>values tableObject workObject n 0 (lift v)))
    (table : WordArrayRep before tableObject (n/2*12) (fun _=>0))
    (work : WordArrayRep before workObject 512 workData) (different : tableObject≠workObject)
    (rootDigits : ∀c : Fin 2,∀d,d<5 → workData (128+6*c.val+d)<1000000000)
    (rootSigns : ∀c : Fin 2,workData (128+6*c.val+5)≤1)
    (rootValue : ComplexSource.pair workData 128=FFT.IntegerModel.root n) :
    ∃after newId tableData finalWork,
      ExecList context before [unitAssignment,jDeclaration,loop] .normal after ∧
      View after tableObject workObject n (combinedIds oldIds newId) before.scope (n/2) tableData finalWork (FFT.IntegerModel.root n) ∧
      Frame before.nextObject before after [tableObject,workObject] ∧
      (∀k,k<512 →46≤k → finalWork k=workData k) ∧
      (∀other flow,ExecList context before [unitAssignment,jDeclaration,loop] flow other → flow=.normal ∧ other=after) := by
  obtain ⟨middle,newId,setup,hm,initFrame,fresh⟩:=initialize_table context before tableObject workObject n oldIds workData
    original well locals table work different rootDigits rootSigns rootValue
  obtain ⟨after,tableData,finalWork,run,ha,loopFrame,outWork,every⟩:=loop_execution context functions (n/2-1) hm (by have a:=hm.active;omega)
  have enlarged : Frame before.nextObject before middle [tableObject,workObject] := by
    refine ⟨initFrame.well,initFrame.fresh,initFrame.nextObject,initFrame.nextScope,initFrame.mode,initFrame.foreign,?_⟩
    intro id old away
    exact initFrame.outside id old (by simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at away;simp only [List.mem_singleton];exact away.1)
  have restricted : Frame before.nextObject middle after [tableObject,workObject] := by
    refine ⟨loopFrame.well,enlarged.fresh.trans loopFrame.nextObject,loopFrame.nextObject,loopFrame.nextScope,loopFrame.mode,loopFrame.foreign,?_⟩
    intro id old away
    apply loopFrame.outside id (lt_of_lt_of_le old initFrame.nextObject)
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or,combinedIds] at away ⊢
    exact ⟨away.1,away.2,by omega⟩
  have allRun : ExecList context before [unitAssignment,jDeclaration,loop] .normal after:=
    append_normal setup (.cons run .nil)
  exact ⟨after,newId,tableData,finalWork,allRun,ha,enlarged.trans restricted,outWork,fun _ _ arbitrary=>prefix_loop_every setup every arbitrary⟩

#print axioms construct_table
end RH080Next.FFTPV.TwiddleSource
