/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainLocalsTransport
import FFTMainFinalSource
import FFTMainFailurePrefix
import FFTNormalizeSource
import FFTAnswerSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainFinish
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource
open MainRootBirth

structure ReturningSegment {F : Type} (context : Context F) (before : State F)
    (statements : List Stmt) (value : Value) (after : State F) : Prop where
  execution : ExecList context before statements (.returned value) after
  every : ∀other flow,ExecList context before statements flow other → flow=.returned value ∧ other=after

theorem append_run {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow}
    (first : ExecList context before xs .normal middle) (last : ExecList context middle ys flow after) :
    ExecList context before (xs++ys) flow after := by
  induction xs generalizing before with
  | nil=>cases first;exact last
  | cons s ss ih=>
    cases first with
    | cons head tail=>exact .cons head (ih tail)
    | abrupt head impossible=>exact False.elim (impossible rfl)

theorem then_return {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {value : Value}
    (first : NormalSegment context before xs middle)
    (last : ReturningSegment context middle ys value after) :
    ReturningSegment context before (xs++ys) value after := by
  refine ⟨append_run first.execution last.execution,?_⟩
  intro other flow actual
  rcases MainAllocation.execution_append_cases xs ys actual with normal|abrupt
  · obtain ⟨current,prefixRun,suffix⟩:=normal
    obtain ⟨_,same⟩:=first.every _ _ prefixRun
    subst current
    exact last.every _ _ suffix
  · exact False.elim (abrupt.1 (first.every _ _ abrupt.2).1)

theorem frame_widen {F : Type} {before after : State F} {cutoff : Nat} {xs ys : List Nat}
    (frame : Frame cutoff before after xs) (subset : ∀i,i∈xs → i∈ys) :
    Frame cutoff before after ys :=
  ⟨frame.well,frame.fresh,frame.nextObject,frame.nextScope,frame.mode,frame.foreign,
    fun i old away=>frame.outside i old (fun member=>away (subset i member))⟩

def normalizeLift : NormalizeSource.Var → FullVar
  | .n=>some (.inl none) | .total=>some (.inr .total)
  | .quad=>some (.inr .quad) | .status=>none

theorem normalize_lift_injective : Function.Injective normalizeLift := by
  intro a b same
  cases a <;> cases b <;> simp_all [normalizeLift]

def normalizeIds (nId : Nat) (oldIds : MainAllocation.Role → Nat) (base status : Nat) :
    NormalizeSource.Var → Nat:=fun v=>fullIds nId oldIds base status (normalizeLift v)

theorem normalize_locals {F : Type} {state : State F} {n nId owner base status : Nat}
    {objects oldIds : MainAllocation.Role → Nat}
    (locals : FullMainLocals state n nId owner objects oldIds base status) :
    Locals state NormalizeSource.name NormalizeSource.type (normalizeIds nId oldIds base status)
      owner (NormalizeSource.values (objects .work) n) := by
  refine ⟨?_,?_,?_,locals.bound⟩
  · intro v;have h:=locals.lookup (normalizeLift v);cases v <;> exact h
  · intro v;have h:=locals.slots (normalizeLift v);cases v <;> exact h
  · intro a b same
    exact normalize_lift_injective (locals.distinct same)

def answerLift : AnswerSource.InputVar → FullVar
  | .total=>some (.inr .total) | .quad=>some (.inr .quad) | .status=>none
theorem answer_lift_injective : Function.Injective answerLift := by
  intro a b same
  cases a <;> cases b <;> simp_all [answerLift]

def answerIds (nId : Nat) (oldIds : MainAllocation.Role → Nat) (base status : Nat) :
    AnswerSource.InputVar → Nat:=fun v=>fullIds nId oldIds base status (answerLift v)

theorem answer_locals {F : Type} {state : State F} {n nId owner base status : Nat}
    {objects oldIds : MainAllocation.Role → Nat}
    (locals : FullMainLocals state n nId owner objects oldIds base status) :
    Locals state (fun v=>AnswerSource.name (AnswerSource.inputLift v))
      (fun v=>AnswerSource.type (AnswerSource.inputLift v)) (answerIds nId oldIds base status)
      owner (fun v=>AnswerSource.values (objects .work) 0 0 0 (AnswerSource.inputLift v)) := by
  refine ⟨?_,?_,?_,locals.bound⟩
  · intro v;have h:=locals.lookup (answerLift v);cases v <;> exact h
  · intro v;have h:=locals.slots (answerLift v);cases v <;> exact h
  · intro a b same
    exact answer_lift_injective (locals.distinct same)

theorem full_name_ne_answer (v : FullVar) : fullName v≠"answer" := by
  cases v with
  | none=>decide
  | some v=>
    cases v with
    | inl v=>cases v with
      | none=>decide
      | some r=>cases r <;> decide
    | inr p=>cases p <;> decide

theorem answer_lookup {F : Type} {context : Context F} {before after : State F} {allowance : Nat}
    (actual : ExecList context before [AnswerSource.answerDeclaration,AnswerSource.statusBranch allowance] .normal after)
    (v : FullVar) : after.environment.lookup (fullName v)=before.environment.lookup (fullName v) := by
  cases actual with
  | abrupt first impossible=>exact False.elim (impossible rfl)
  | cons first rest=>
    have firstLookup:=MainTransport.pure_declaration_lookup (by trivial) (full_name_ne_answer v) first
    cases rest with
    | abrupt second impossible=>exact False.elim (impossible rfl)
    | cons second rest=>
      cases rest
      rw [(AnswerSource.status_environment_scope second).1,firstLookup]

def magnitudeAt (data : Nat → Nat) (start : Nat) : Nat:=
  FFT.Limbs.magnitude 1000000000 6 (fun k=>data (start+k))
def scalarConvert (m : Nat) : Nat:=if m<1000000000000000000 then m else AnswerSource.sentinel
def finishValue (fap : Bool) (n total quad : Nat) : Nat:=
  AnswerSource.computed (scalarConvert total) (scalarConvert (NormalizeSource.quadValue quad n))
    AnswerSource.sentinel (AnswerSource.profileAllowance fap)

theorem answer_result_eq (data : Nat → Nat) (fap : Bool)
    (totalDigits : ∀k,k<6 → data (192+k)<1000000000)
    (quadDigits : ∀k,k<6 → data (208+k)<1000000000) :
    AnswerSource.result data (AnswerSource.profileAllowance fap)=
      AnswerSource.computed (scalarConvert (magnitudeAt data 192))
        (scalarConvert (magnitudeAt data 208)) AnswerSource.sentinel (AnswerSource.profileAllowance fap) := by
  unfold AnswerSource.result AnswerSource.firstValue AnswerSource.secondValue
  rw [ConvertBoundSource.converted_magnitude data 192 totalDigits,
    ConvertBoundSource.converted_magnitude data 208 quadDigits]
  rfl

theorem finishValue_fits (fap : Bool) (n total quad : Nat) : finishValue fap n total quad<2^64 :=
  AnswerSource.computed_fits _ _ _ _ (by norm_num [AnswerSource.sentinel])
    (by cases fap <;> norm_num [AnswerSource.profileAllowance])

#print axioms then_return
#print axioms normalize_locals
#print axioms answer_locals
#print axioms answer_lookup
#print axioms answer_result_eq
end RH080Next.FFTPV.MainFinish
