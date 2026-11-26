/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixSum
import FFTMainSuffixDropEnvironment
import FFTNormalizeSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

def dropLift : DropTwoSource.InitVar → OutputSumSource.Var
  | .total => .total | .i => .i | .status => .status

def dropIds (pointerBase status iId : Nat) : DropTwoSource.InitVar → Nat
  | .total => pointerBase+2 | .i => iId | .status => status

def normalizeLift : NormalizeSource.Var → FullVar
  | .n => some (.inl none) | .total => some (.inr .total)
  | .quad => some (.inr .quad) | .status => none

def normalizeIds (nId pointerBase status : Nat) : NormalizeSource.Var → Nat
  | .n => nId | .total => pointerBase+2 | .quad => pointerBase+3 | .status => status

theorem normalize_parameters {F : Type} {state : State F} {n nId owner pointerBase status : Nat}
    {objects ids : Role → Nat}
    (full : FullMainLocals state n nId owner objects ids pointerBase status) :
    Locals state NormalizeSource.name NormalizeSource.type (normalizeIds nId pointerBase status) owner
      (NormalizeSource.values (objects .work) n) := by
  have injective : Function.Injective normalizeLift := by intro a b h;cases a <;> cases b <;> simp_all [normalizeLift]
  have d := full.distinct.comp injective
  have same : normalizeIds nId pointerBase status = fullIds nId ids pointerBase status ∘ normalizeLift := by
    funext v;cases v <;> rfl
  refine ⟨?_,?_,by rw [same];exact d,full.bound⟩
  · intro v;have h := full.lookup (normalizeLift v);cases v <;> exact h
  · intro v;have h := full.slots (normalizeLift v);cases v <;> exact h

/-- All actual old main slots differ from the real sum counter. Pointer slots
are distinguished by their actual stored values; n/status use the actual sum
Locals injectivity. -/
theorem full_main_i_distinct {F : Type} {state : State F} {n nId owner pointerBase status iId : Nat}
    {objects ids : Role → Nat} {outputData workData : Nat → Nat} {samples : Nat → FFT.IntegerModel.CInt}
    (full : FullMainLocals state n nId owner objects ids pointerBase status)
    (sum : OutputSumSource.View state (objects .output) (objects .work) n
      (sumIds nId ids pointerBase status iId) owner n outputData workData samples) :
    ∀v,fullIds nId ids pointerBase status v≠iId := by
  intro v
  cases v with
  | none =>
    intro same
    have eq : sumIds nId ids pointerBase status iId .status=sumIds nId ids pointerBase status iId .i := same
    have bad := sum.locals.distinct eq
    cases bad
  | some v => cases v with
    | inl v => cases v with
      | none =>
        intro same
        have eq : sumIds nId ids pointerBase status iId .n=sumIds nId ids pointerBase status iId .i := same
        have bad := sum.locals.distinct eq
        cases bad
      | some r => cases r <;> exact MultiplyParameters.pointer_integer_slots_different (full.slots _) (sum.locals.slots .i)
    | inr p => cases p <;> exact MultiplyParameters.pointer_integer_slots_different (full.slots _) (sum.locals.slots .i)

theorem full_name_ne_lost (v : FullVar) : fullName v≠"lost" := by
  cases v with
  | none => decide
  | some v => cases v with
    | inl v => cases v with
      | none => decide
      | some r => cases r <;> decide
    | inr p => cases p <;> decide

#print axioms normalize_parameters
#print axioms full_main_i_distinct
end RH080Next.FFTPV.MainSuffix
