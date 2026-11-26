/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainMemoryContract
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainCounters
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource

def zeroLiteral : Expr:=.literal (.integer 0 "ULL")
def declaration (cname : String) : Stmt:=.declare .u64 cname (some zeroLiteral)
def reset (cname : String) : Stmt:=.assign (.variable cname) zeroLiteral

theorem declaration_and_reset {F : Type} (context : Context F) (before : State F) (cname : String)
    (well : WellScoped before) :
    ∃after,NormalSegment context before [declaration cname,reset cname] after ∧
      after.environment=(cname,scalarPointer before.nextObject .u64)::before.environment ∧
      Slot after before.nextObject before.scope .u64 (.integer (integer64 0)) ∧
      Frame before.nextObject before after [] := by
  have storage:=ZeroFrame.u64_storable 0 (by norm_num)
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists well .u64 cname (.integer (integer64 0)) storage
  have d:=declare_storable storage storage.converted declared
  have lookup : after.environment.lookup cname=some (scalarPointer before.nextObject .u64) := by
    rw [d.environment]
    simp [List.lookup]
  have assigned : Exec context after (reset cname) .normal after :=
    .assign (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) (.variable lookup)
      (StatusCall.slot_store_same d.slot)
  have run : ExecList context before [declaration cname,reset cname] .normal after :=
    .cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) declared)
      (.cons assigned .nil)
  exact ⟨after,NormalSegment.pure run (by intro s hs;simp only [List.mem_cons,List.not_mem_nil,or_false] at hs;rcases hs with rfl|rfl <;> trivial),
    d.environment,d.slot,ApplicationBirthFrame.declare_frame before.nextObject [] well (le_refl _) declared⟩

/-- Real typed scalar store, from an arbitrary initialized u64 source slot. -/
theorem u64_store_exists {F : Type} {before : State F} {id owner : Nat} {old : Value}
    (slot : Slot before id owner .u64 old) (value : Nat) (fit : value<2^64) :
    ∃after,before.store (scalarPointer id .u64) (.integer (integer64 value))=some after := by
  have bytes : old.byteSize=8 := by
    have eq:=slot.storable.typeWidth
    change some 8=some old.byteSize at eq
    exact (Option.some.inj eq).symm
  have object : before.objects id=some (scalarObject owner 8 old) := by
    simpa only [bytes] using slot.object
  simp [State.store,scalarPointer,object,scalarObject,State.accessible,CType.byteSize,convert64 value fit]

/-- Actual j=0 or i=0 reset, including full source determinism and every
unaffected old caller object. It does not assume the counter was already zero. -/
theorem reset_execution {F : Type} (context : Context F) (before : State F) (cname : String)
    (id owner : Nat) (old : Value) (well : WellScoped before)
    (lookup : before.environment.lookup cname=some (scalarPointer id .u64))
    (slot : Slot before id owner .u64 old) :
    ∃after,NormalSegment context before [reset cname] after ∧
      Slot after id owner .u64 (.integer (integer64 0)) ∧
      Frame before.nextObject before after [id] ∧ after.environment=before.environment := by
  obtain ⟨after,stored⟩:=u64_store_exists slot 0 (by norm_num)
  have exec : Exec context before (reset cname) .normal after :=
    .assign (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) (.variable lookup) stored
  have frame:=ApplicationBirthFrame.store_frame before.nextObject [id] well (le_refl _)
    (by simp [scalarPointer]) stored
  exact ⟨after,NormalSegment.pure (.cons exec .nil) (by intro s hs;have eq:=List.mem_singleton.mp hs;subst s;trivial),
    slot.store (ZeroFrame.u64_storable 0 (by norm_num)) stored,frame,(SourceLocals.store_frame stored).1⟩

theorem actual_w4_sum_counter : ((MainAllocation.bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 23).take 2=
    [declaration "i",reset "i"] := by rfl
theorem actual_fap_sum_counter : ((MainAllocation.bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 23).take 2=
    [declaration "i",reset "i"] := by rfl

theorem actual_w4_loader_reset : (MainAllocation.bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast)[20]?=some (reset "j") := by rfl
theorem actual_fap_loader_reset : (MainAllocation.bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast)[20]?=some (reset "j") := by rfl

#print axioms declaration_and_reset
#print axioms reset_execution
#print axioms actual_w4_sum_counter
#print axioms actual_fap_sum_counter
end RH080Next.FFTPV.MainCounters
