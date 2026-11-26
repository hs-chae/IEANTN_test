/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDropTwoInitialization
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DropTwoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

def statements : List Stmt:=[lostDeclaration,iReset,loop,clear 4,clear 5,roundingBranch]

theorem actual_six_statements : ((ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body).drop 26).take 6=statements:=by rfl

private theorem append_normal {F : Type} {context : Context F} {before middle after : State F}
    {a b : List Stmt} {flow : Flow} (first : ExecList context before a .normal middle)
    (second : ExecList context middle b flow after) : ExecList context before (a++b) flow after:=by
  induction a generalizing before with
  | nil=>cases first;exact second
  | cons x xs ih=>
    cases first with
    | cons run rest=>exact .cons run (ih rest)
    | abrupt _ bad=>exact False.elim (bad rfl)

private theorem list_effect {F : Type} {context : Context F} {before after : State F}
    {xs : List Stmt} (run : ExecList context before xs .normal after)
    (only : ∀stmt∈xs,SourceNoAlloc.Only stmt) (well : WellScoped before) : SourceNoAlloc.Effect before after:=by
  induction xs generalizing before with
  | nil=>cases run;exact SourceNoAlloc.Effect.refl well
  | cons x xs ih=>
    cases run with
    | abrupt _ bad=>exact False.elim (bad rfl)
    | cons first rest=>
      have effect:=SourceNoAlloc.exec_effect first (only x (by simp)) well
      exact effect.trans (ih rest (fun stmt member=>only stmt (by simp [member])) effect.well)

private theorem prefix_last_every {F : Type} {context : Context F} {before middle after other : State F}
    {xs : List Stmt} {last : Stmt} {flow : Flow}
    (unique : ∀stmt∈xs,CompareSource.Unique context stmt)
    (setup : ExecList context before xs .normal middle)
    (every : ∀state flow,Exec context middle last flow state → flow=.normal ∧ state=after)
    (run : ExecList context before (xs++[last]) flow other) : flow=.normal ∧ other=after := by
  induction xs generalizing before with
  | nil=>
    cases setup
    cases run with
    | abrupt actual abnormal=>exact False.elim (abnormal (every _ _ actual).1)
    | cons actual tail=>
      obtain ⟨_,eqs⟩:=every _ _ actual
      cases eqs
      cases tail
      exact ⟨rfl,rfl⟩
  | cons x xs ih=>
    cases setup with
    | abrupt _ bad=>exact False.elim (bad rfl)
    | cons first rest=>
      cases run with
      | abrupt actual abnormal=>
        have eq:=(unique x (by simp)) first actual
        exact False.elim (abnormal eq.1.symm)
      | cons actual tail=>
        obtain ⟨_,eqs⟩:=(unique x (by simp)) first actual
        cases eqs
        exact ih (fun stmt member=>unique stmt (by simp [member])) rest tail

/-- Full actual source normalization of the unsigned FFT magnitude sum: real
lost-limb declaration, overlapping forward shift, upper zeros and conditional
source-verified increment. The result is the true upward quotient by10^18. -/
theorem drop_two_total {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast)
    (before : State F) (workObject previous : Nat) (ids : InitVar→Nat) (old : Nat→Nat) (well : WellScoped before)
    (params : Locals before (fun v=>name (lift v)) (fun v=>type (lift v)) ids before.scope
      (fun v=>values workObject old previous (lift v)))
    (array : WordArrayRep before workObject 512 old) (digits : ∀k,k<6 → old (192+k)<base) :
    ∃after newId,ExecList context before statements .normal after ∧
      WordArrayRep after workObject 512 (roundData old 192) ∧
      Locals after name type (combinedIds ids newId) before.scope (values workObject old 4) ∧
      Frame before.nextObject before after [workObject,ids InitVar.i] ∧
      FFT.Limbs.magnitude base 6 (fun k=>roundData old 192 (192+k))=
        FFT.Limbs.ceilQuotient (FFT.Limbs.magnitude base 6 (fun k=>old (192+k))) (base^2) ∧
      (∀other flow,ExecList context before statements flow other → flow=.normal ∧ other=after) := by
  obtain ⟨initialized,newId,setup,initialView,setupFrame,fresh⟩:=initialize_drop context before workObject previous ids old well params array digits
  obtain ⟨shiftedState,shiftRun,shiftView,shiftFrame,_⟩:=loop_execution context 4 initialView (by norm_num)
  obtain ⟨cleared,clearRun,clearArray,clearParams,clearWell,clearFrame⟩:=clear_execution context shiftView
  obtain ⟨after,roundRun,roundArray,roundParams,roundFrame,everyRound⟩:=rounding_execution context selected clearArray clearParams shiftView.separate digits clearWell
  have shiftOnly : SourceNoAlloc.Only loop:=by
    simp [loop,condition,loopBody,move,sourceIndex,advance,SourceNoAlloc.Only,SourcePure.CallFree]
  have shiftEffect:=SourceNoAlloc.exec_effect shiftRun shiftOnly initialView.well
  have clearEffect:=list_effect clearRun (by intro stmt member;simp only [List.mem_cons,List.mem_nil_iff,or_false] at member;rcases member with rfl|rfl <;> simp [clear,SourceNoAlloc.Only,SourcePure.CallFree]) shiftView.well
  have firstFrame : Frame before.nextObject before initialized [workObject,ids InitVar.i]:=by
    refine ⟨setupFrame.well,setupFrame.fresh,setupFrame.nextObject,setupFrame.nextScope,setupFrame.mode,setupFrame.foreign,?_⟩
    intro id old away
    exact setupFrame.outside id old (by simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at away;simp only [List.mem_singleton];exact away.2)
  have secondFrame : Frame before.nextObject initialized shiftedState [workObject,ids InitVar.i]:=by
    refine ⟨shiftEffect.well,?_,?_,shiftFrame.nextScope,shiftFrame.mode,shiftEffect.foreign,?_⟩
    · rw [shiftFrame.nextObject];exact setupFrame.fresh
    · rw [shiftFrame.nextObject]
    · intro id old away
      exact shiftFrame.outside id (by simpa only [combinedIds] using away)
  have thirdFrame : Frame before.nextObject shiftedState cleared [workObject,ids InitVar.i]:=by
    refine ⟨clearEffect.well,?_,?_,clearFrame.nextScope,clearFrame.mode,clearEffect.foreign,?_⟩
    · rw [clearFrame.nextObject];exact secondFrame.fresh
    · rw [clearFrame.nextObject]
    · intro id old away
      exact clearFrame.outside id (by simpa only [combinedIds] using away)
  have lastFrame : Frame before.nextObject cleared after [workObject,ids InitVar.i]:=by
    refine ⟨roundFrame.well,(firstFrame.trans secondFrame |>.trans thirdFrame).fresh.trans roundFrame.nextObject,
      roundFrame.nextObject,roundFrame.nextScope,roundFrame.mode,roundFrame.foreign,?_⟩
    intro id old away
    exact roundFrame.outside id (lt_of_lt_of_le old (firstFrame.trans secondFrame |>.trans thirdFrame).nextObject)
      (by simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at away;simp only [List.mem_singleton];exact away.1)
  have all : ExecList context before statements .normal after:=
    append_normal setup (.cons shiftRun (append_normal clearRun (.cons roundRun .nil)))
  refine ⟨after,newId,all,roundArray,roundParams,firstFrame.trans (secondFrame.trans (thirdFrame.trans lastFrame)),roundData_magnitude digits,?_⟩
  intro other flow arbitrary
  apply prefix_last_every (xs:=[lostDeclaration,iReset,loop,clear 4,clear 5]) ?_
    (append_normal setup (.cons shiftRun clearRun)) everyRound arbitrary
  intro stmt member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl
  · exact fun first second=>PureDeterminism.simple_unique (by simp [lostDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact fun first second=>PureDeterminism.simple_unique (by simp [iReset,PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact loop_unique context
  · exact fun first second=>PureDeterminism.simple_unique (by simp [clear,PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact fun first second=>PureDeterminism.simple_unique (by simp [clear,PureDeterminism.Simple,SourcePure.CallFree]) first second

#print axioms actual_six_statements
#print axioms drop_two_total
end RH080Next.FFTPV.DropTwoSource
