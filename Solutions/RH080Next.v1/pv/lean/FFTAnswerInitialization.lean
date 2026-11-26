/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTAnswerStatus
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AnswerSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

inductive InputVar where | total | quad | status deriving DecidableEq

def inputLift : InputVar→Var | .total=>.total | .quad=>.quad | .status=>.status

def mainIds (ids : InputVar→Nat) (answerId : Nat) : MainVar→Nat
  | .total=>ids .total | .quad=>ids .quad | .status=>ids .status | .answer=>answerId

/-- The original answer=UINT64_MAX declaration is executed; it is not an
assumed initialized local or an unverified hardcoded numerical answer. -/
theorem initialize_answer {F : Type} (context : Context F) (before : State F) (workObject : Nat)
    (ids : InputVar→Nat) (data : Nat→Nat) (well : WellScoped before)
    (params : Locals before (fun v=>name (inputLift v)) (fun v=>type (inputLift v)) ids before.scope
      (fun v=>values workObject 0 0 0 (inputLift v)))
    (array : WordArrayRep before workObject 512 data) (separate : ∀v,workObject≠ids v) :
    ∃after answerId,Exec context before answerDeclaration .normal after ∧
      Locals after (fun v=>name (lift v)) (fun v=>type (lift v)) (mainIds ids answerId) before.scope
        (fun v=>values workObject 0 0 sentinel (lift v)) ∧
      WordArrayRep after workObject 512 data ∧ Frame before.nextObject before after [] ∧
      before.nextObject≤answerId ∧ after.environment=("answer",scalarPointer answerId .u64)::before.environment ∧
      (∀other flow,Exec context before answerDeclaration flow other → flow=.normal ∧ other=after) := by
  have fits : sentinel<2^64:=by norm_num [sentinel]
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists well .u64 "answer" (.integer (integer64 sentinel)) (ZeroFrame.u64_storable _ fits)
  have birth:=declare_storable (ZeroFrame.u64_storable _ fits) (by rfl) declared
  have oldParams:=ApplicationBirthFrame.locals_declare_old well params (by intro v;cases v <;> decide) birth
  have oldWork:=well.objectIds _ _ array.2.1
  have locs : Locals after (fun v=>name (lift v)) (fun v=>type (lift v)) (mainIds ids before.nextObject) before.scope
      (fun v=>values workObject 0 0 sentinel (lift v)) := by
    constructor
    · intro v;cases v with
      | total=>exact oldParams.lookup InputVar.total
      | quad=>exact oldParams.lookup InputVar.quad
      | status=>exact oldParams.lookup InputVar.status
      | answer=>simp [lift,mainIds,name,type,birth.environment,scalarPointer]
    · intro v;cases v with
      | total=>exact oldParams.slots InputVar.total
      | quad=>exact oldParams.slots InputVar.quad
      | status=>exact oldParams.slots InputVar.status
      | answer=>exact birth.slot
    · intro v w equal
      have bt:=well.objectIds _ _ (params.slots InputVar.total).object
      have bq:=well.objectIds _ _ (params.slots InputVar.quad).object
      have bs:=well.objectIds _ _ (params.slots InputVar.status).object
      have distinct : ∀v w : InputVar,v≠w → ids v≠ids w:=fun v w ne eq=>ne (params.distinct eq)
      cases v <;> cases w <;> simp only [mainIds] at equal ⊢
      all_goals first | rfl | exact False.elim (distinct _ _ (by decide) equal) | omega
    · rw [birth.nextScope];exact params.bound
  have rep : WordArrayRep after workObject 512 data:=
    ⟨birth.mode.trans array.1,(birth.outside workObject (by omega)).trans array.2.1,array.2.2⟩
  have run : Exec context before answerDeclaration .normal after:=.declareSome (.literal (.integer sentinel "ULL") _ _ (by rfl)) declared
  exact ⟨after,before.nextObject,run,locs,rep,ApplicationBirthFrame.declare_frame before.nextObject [] well (le_refl _) declared,
    le_refl _,birth.environment,fun other flow arbitrary=>by
      have eq:=PureDeterminism.simple_unique (by simp [answerDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) run arbitrary
      exact ⟨eq.1.symm,eq.2.symm⟩⟩

#print axioms initialize_answer
end RH080Next.FFTPV.AnswerSource
