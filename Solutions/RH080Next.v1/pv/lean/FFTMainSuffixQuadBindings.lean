/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixLoaderBindings
import ExplicitFFTQuadSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

theorem integer_slots_different {F : Type} {state : State F} {a b ownerA ownerB n m : Nat}
    (first : Slot state a ownerA .u64 (.integer (integer64 n)))
    (second : Slot state b ownerB .u64 (.integer (integer64 m))) (different : n≠m) : a≠b := by
  intro same
  subst b
  have values := Option.some.inj (first.read.symm.trans second.read)
  simp only [Value.integer.injEq,integer64,Integer.mk.injEq,true_and] at values
  exact different values

def quadLift : QuadSource.Aux → FullVar
  | .temp => some (.inr .temp) | .quad => some (.inr .quad) | .status => none

def quadIds (pointerBase status : Nat) : QuadSource.Aux → Nat
  | .temp => pointerBase+1 | .quad => pointerBase+3 | .status => status

theorem quad_parameters {F : Type} {state : State F} {n nId owner pointerBase status : Nat}
    {objects ids : Role → Nat}
    (full : FullMainLocals state n nId owner objects ids pointerBase status) :
    Locals state QuadSource.auxName QuadSource.auxType (quadIds pointerBase status) owner (QuadSource.auxValues (objects .work)) := by
  have inj : Function.Injective quadLift := by intro a b h;cases a <;> cases b <;> simp_all [quadLift]
  have same : quadIds pointerBase status=fullIds nId ids pointerBase status ∘ quadLift := by funext v;cases v <;> rfl
  refine ⟨?_,?_,by rw [same];exact full.distinct.comp inj,full.bound⟩
  · intro v;have h:=full.lookup (quadLift v);cases v <;> exact h
  · intro v;have h:=full.slots (quadLift v);cases v <;> exact h

theorem full_main_loader_j_distinct {F : Type} {state : State F} {p : InputLoader.Profile}
    {nId owner pointerBase status jId : Nat} {objects ids : Role → Nat}
    (full : FullMainLocals state p.grid nId owner objects ids pointerBase status)
    (loader : Locals state InputLoader.parameterName InputLoader.parameterType (loaderIds nId ids jId) owner
      (InputLoader.parameterValues ⟨p,objects .data⟩ p.count)) :
    ∀v,fullIds nId ids pointerBase status v≠jId := by
  intro v
  cases v with
  | none =>
    apply integer_slots_different (full.slots none) (loader.slots .j)
    have positive:=p.shape.1;omega
  | some v => cases v with
    | inl v => cases v with
      | none =>
        apply integer_slots_different (full.slots (some (.inl none))) (loader.slots .j)
        have bound:=p.shape.2.1;omega
      | some r => cases r <;> exact MultiplyParameters.pointer_integer_slots_different (full.slots _) (loader.slots .j)
    | inr p => cases p <;> exact MultiplyParameters.pointer_integer_slots_different (full.slots _) (loader.slots .j)

theorem quad_cross {F : Type} {state : State F} {p : InputLoader.Profile}
    {nId owner pointerBase status jId : Nat} {objects ids : Role → Nat}
    (full : FullMainLocals state p.grid nId owner objects ids pointerBase status)
    (jDifferent : ∀v,fullIds nId ids pointerBase status v≠jId) :
    ∀v a,loaderIds nId ids jId v≠quadIds pointerBase status a := by
  intro v a
  cases v with
  | data =>
    have ne : (some (.inl (some Role.data)) : FullVar)≠quadLift a := by cases a <;> decide
    have h:=full.distinct.ne ne
    cases a <;> exact h
  | n =>
    have ne : (some (.inl none) : FullVar)≠quadLift a := by cases a <;> decide
    have h:=full.distinct.ne ne
    cases a <;> exact h
  | j =>
    have h:=(jDifferent (quadLift a)).symm
    cases a <;> exact h

#print axioms integer_slots_different
#print axioms quad_parameters
#print axioms full_main_loader_j_distinct
#print axioms quad_cross
end RH080Next.FFTPV.MainSuffix
