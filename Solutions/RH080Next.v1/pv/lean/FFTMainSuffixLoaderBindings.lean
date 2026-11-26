/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixTable
import FFTMainCounters
import ExplicitFFTInputLoaderSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

theorem full_main_j_distinct {F : Type} {state : State F} {n nId owner pointerBase status jId : Nat}
    {objects ids : Role→Nat} {tableData workData : Nat→Nat}
    (full : FullMainLocals state n nId owner objects ids pointerBase status)
    (view : TwiddleSource.View state (objects .twiddle) (objects .work) n
      (TwiddleSource.combinedIds (tableOldIds nId ids pointerBase status) jId) owner (n/2)
      tableData workData (FFT.IntegerModel.root n)) :
    ∀v,fullIds nId ids pointerBase status v≠jId := by
  intro v
  cases v with
  | none=>
    intro same
    have eq : TwiddleSource.combinedIds (tableOldIds nId ids pointerBase status) jId .status=TwiddleSource.combinedIds (tableOldIds nId ids pointerBase status) jId .j:=same
    have bad:=view.locals.distinct eq
    cases bad
  | some v=>
    cases v with
    | inl v=>
      cases v with
      | none=>
        intro same
        have eq : TwiddleSource.combinedIds (tableOldIds nId ids pointerBase status) jId .n=TwiddleSource.combinedIds (tableOldIds nId ids pointerBase status) jId .j:=same
        have bad:=view.locals.distinct eq
        cases bad
      | some r=>
        cases r <;> exact MultiplyParameters.pointer_integer_slots_different (full.slots _) (view.locals.slots .j)
    | inr p=>
      cases p <;> exact MultiplyParameters.pointer_integer_slots_different (full.slots _) (view.locals.slots .j)

def loaderIds (nId : Nat) (ids : Role→Nat) (jId : Nat) : InputLoader.Parameter→Nat
  | .data=>ids .data | .n=>nId | .j=>jId

/-- The loader's actual three input variables are selected from genuine main
slots and the actual reset j slot; no initialized source binding is assumed. -/
theorem loader_parameters {F : Type} {state : State F} {p : InputLoader.Profile}
    {nId owner pointerBase status jId : Nat} {objects ids : Role→Nat}
    (full : FullMainLocals state p.grid nId owner objects ids pointerBase status)
    (lookup : state.environment.lookup "j"=some (scalarPointer jId .u64))
    (slot : Slot state jId owner .u64 (.integer (integer64 0)))
    (nDifferent : nId≠jId) :
    Locals state InputLoader.parameterName InputLoader.parameterType (loaderIds nId ids jId) owner
      (InputLoader.parameterValues ⟨p,objects .data⟩ 0) := by
  have dataN : ids .data≠nId:=by
    exact full.distinct.ne (by decide : (some (.inl (some Role.data)) : FullVar)≠some (.inl none))
  have dataJ : ids .data≠jId:=
    MultiplyParameters.pointer_integer_slots_different (full.slots (some (.inl (some .data)))) slot
  refine ⟨?_,?_,?_,full.bound⟩
  · intro v
    cases v with
    | data=>exact full.lookup (some (.inl (some .data)))
    | n=>exact full.lookup (some (.inl none))
    | j=>exact lookup
  · intro v
    cases v with
    | data=>exact full.slots (some (.inl (some .data)))
    | n=>exact full.slots (some (.inl none))
    | j=>exact slot
  · intro a b same
    cases a <;> cases b <;> simp_all [loaderIds]

#print axioms full_main_j_distinct
#print axioms loader_parameters
end RH080Next.FFTPV.MainSuffix
