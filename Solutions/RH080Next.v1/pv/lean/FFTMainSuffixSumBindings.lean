/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixScopes
import FFTMainCounters
import FFTOutputSumSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

def sumLift : OutputSumSource.Var→Option FullVar
  | .n=>some (some (.inl none)) | .output=>some (some (.inl (some .output)))
  | .total=>some (some (.inr .total)) | .status=>some none | .i=>none

def sumIds (nId : Nat) (ids : Role→Nat) (pointerBase status iId : Nat) : OutputSumSource.Var→Nat
  | .i=>iId | .n=>nId | .output=>ids .output | .total=>pointerBase+2 | .status=>status

theorem full_name_ne_i (v : FullVar) : fullName v≠"i" := by
  cases v with
  | none=>decide
  | some v=>cases v with
    | inl v=>cases v with
      | none=>decide
      | some r=>cases r <;> decide
    | inr p=>cases p <;> decide

theorem counter_scope {F : Type} {context : Context F} {before after : State F} {name : String}
    (run : ExecList context before [MainCounters.declaration name,MainCounters.reset name] .normal after) :
    after.scope=before.scope:=by
  cases run with
  | abrupt h no=>exact False.elim (no rfl)
  | cons h rest=>
    have a:=pure_declaration_scope (by trivial) h
    cases rest with
    | abrupt h no=>exact False.elim (no rfl)
    | cons h rest=>cases rest;exact (pure_assignment_scope (by trivial) (by trivial) h).trans a

theorem sum_parameters {F : Type} {before after : State F} {n nId owner pointerBase status : Nat}
    {objects ids : Role→Nat}
    (full : FullMainLocals before n nId owner objects ids pointerBase status)
    (well : WellScoped before) (scope : before.scope=owner)
    (environment : after.environment=("i",scalarPointer before.nextObject .u64)::before.environment)
    (iSlot : Slot after before.nextObject before.scope .u64 (.integer (integer64 0)))
    (frame : Frame before.nextObject before after []) :
    FullMainLocals after n nId owner objects ids pointerBase status ∧
    Locals after OutputSumSource.name OutputSumSource.type (sumIds nId ids pointerBase status before.nextObject) owner
      (OutputSumSource.values (objects .output) (objects .work) n 0) := by
  have old : FullMainLocals after n nId owner objects ids pointerBase status:=by
    apply MainTransport.locals_of_frame well full frame
    · intro v;rw [environment];simp only [List.lookup,beq_eq_false_iff_ne.mpr (full_name_ne_i v)]
    · intro v;simp
  let extended : Option FullVar→Nat:=fun v=>match v with | none=>before.nextObject | some v=>fullIds nId ids pointerBase status v
  have oldBound : ∀v,fullIds nId ids pointerBase status v<before.nextObject:=
    fun v=>well.objectIds _ _ (full.slots v).object
  have injective : Function.Injective extended:=by
    intro a b same
    cases a with
    | none=>cases b with
      | none=>rfl
      | some b=>have bound:=oldBound b;change before.nextObject=fullIds nId ids pointerBase status b at same;omega
    | some a=>cases b with
      | none=>have bound:=oldBound a;change fullIds nId ids pointerBase status a=before.nextObject at same;omega
      | some b=>exact congrArg some (full.distinct same)
  have liftInjective : Function.Injective sumLift:=by intro a b same;cases a <;> cases b <;> simp_all [sumLift]
  have distinct : Function.Injective (sumIds nId ids pointerBase status before.nextObject):=by
    have same : sumIds nId ids pointerBase status before.nextObject=extended ∘ sumLift:=by funext v;cases v <;> rfl
    rw [same]
    exact injective.comp liftInjective
  refine ⟨old,⟨?_,?_,distinct,old.bound⟩⟩
  · intro v
    cases v with
    | n=>exact old.lookup (some (.inl none))
    | output=>exact old.lookup (some (.inl (some .output)))
    | total=>exact old.lookup (some (.inr .total))
    | status=>exact old.lookup none
    | i=>rw [environment];simp [List.lookup,OutputSumSource.name,OutputSumSource.type,sumIds]
  · intro v
    cases v with
    | n=>exact old.slots (some (.inl none))
    | output=>exact old.slots (some (.inl (some .output)))
    | total=>exact old.slots (some (.inr .total))
    | status=>exact old.slots none
    | i=>simpa only [scope,sumIds,OutputSumSource.type,OutputSumSource.values] using iSlot

#print axioms full_name_ne_i
#print axioms counter_scope
#print axioms sum_parameters
end RH080Next.FFTPV.MainSuffix
