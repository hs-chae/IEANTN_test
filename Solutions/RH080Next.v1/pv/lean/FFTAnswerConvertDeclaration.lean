/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTAnswerLogic
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AnswerSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

def convertDeclaration (variableName declarationName : String) : Stmt:=
  .declare .u64 declarationName (some (.call "convert_bound" [.variable variableName,.literal (.integer 6 "ULL")]))

/-- Actual source callee execution is followed by the real automatic
first/second declaration; no conversion result or initialized local is assumed. -/
theorem convert_declaration {F : Type} (context : Context F)
    (selected : findFunction context.program "convert_bound"=some convert_bound_ast)
    (before : State F) (workObject start pointerId pointerOwner : Nat) (data : Nat→Nat)
    (variableName declarationName : String)
    (lookup : before.environment.lookup variableName=some (scalarPointer pointerId (.pointer .u64)))
    (pointer : Slot before pointerId pointerOwner (.pointer .u64) (.pointer (wordPointer workObject start)))
    (array : WordArrayRep before workObject 512 data) (bound : start+6≤512)
    (digits : ∀k,k<6 → data (start+k)<1000000000) (well : WellScoped before) :
    ∃after newId,Exec context before (convertDeclaration variableName declarationName) .normal after ∧
      Slot after newId before.scope .u64 (.integer (integer64 (ConvertBoundSource.result data start))) ∧
      after.environment=(declarationName,scalarPointer newId .u64)::before.environment ∧
      after.scope=before.scope ∧ before.nextObject≤newId ∧
      WordArrayRep after workObject 512 data ∧ Frame before.nextObject before after [] ∧
      (∀other flow,Exec context before (convertDeclaration variableName declarationName) flow other → flow=.normal ∧ other=after) := by
  obtain ⟨middle,called,rep,frame,every⟩:=ConvertBoundSource.convert_bound_total context selected before workObject 512 start data well array bound digits
  have fits:=ConvertBoundSource.result_fits data start digits
  have args : Args context before [.variable variableName,.literal (.integer 6 "ULL")]
      [.pointer (wordPointer workObject start),.integer (integer64 6)] before := by
    refine .ordered (List.Perm.refl _) (.cons (.variable lookup pointer.read) (.cons (.literal (.integer 6 "ULL") _ (.integer (integer64 6)) (by rfl)) .nil)) ?_
    exact .cons rfl (.cons rfl .nil)
  have storable:=ZeroFrame.u64_storable (ConvertBoundSource.result data start) fits
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists frame.frame.well .u64 declarationName (.integer (integer64 (ConvertBoundSource.result data start))) storable
  have birth:=declare_storable storable storable.converted declared
  have run : Exec context before (convertDeclaration variableName declarationName) .normal after:=.declareSome (.call args called) declared
  have oldWork : workObject<middle.nextObject:=frame.frame.well.objectIds _ _ rep.2.1
  have afterRep : WordArrayRep after workObject 512 data:=
    ⟨birth.mode.trans rep.1,(birth.outside workObject (by omega)).trans rep.2.1,rep.2.2⟩
  have lastFrame:=ApplicationBirthFrame.declare_frame before.nextObject [] frame.frame.well frame.frame.fresh declared
  refine ⟨after,middle.nextObject,run,?_,?_,birth.scope.trans frame.scope,frame.frame.nextObject,afterRep,frame.frame.trans lastFrame,?_⟩
  · simpa only [frame.scope] using birth.slot
  · simpa only [scalarPointer,frame.environment] using birth.environment
  · intro other flow arbitrary
    cases arbitrary with
    | declareSome actual actualDecl=>
      obtain ⟨eqv,eqs⟩:=StatusCall.call_eval_unique
        (by intro e member;simp only [List.mem_cons,List.mem_nil_iff,or_false] at member;rcases member with rfl|rfl <;> trivial)
        args (fun state result callRun=>by have eq:=every result state callRun;exact eq) actual
      rw [eqv,eqs] at actualDecl
      exact ⟨rfl,Option.some.inj (actualDecl.symm.trans declared)⟩

#print axioms convert_declaration
end RH080Next.FFTPV.AnswerSource
