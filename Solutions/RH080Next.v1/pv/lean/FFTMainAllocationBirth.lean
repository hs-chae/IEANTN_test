/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainAllocationRaw
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

/-- An actual calloc expression followed by its actual pointer declaration.
The new byte array is born before the automatic pointer variable. -/
theorem calloc_pointer_birth {F : Type} (context : Context F) {before : State F}
    {countExpr : Expr} {length : Nat} (cname : String)
    (absent : findFunction context.program "calloc"=none) (memory : HasMemory context)
    (well : WellScoped before) (host : before.mode=.host) (byteFit : length*8<2^64)
    (countEval : Eval context before countExpr (.integer (integer64 length)) before) :
    ∃after pointerId,Exec context before (.declare (.pointer .u64) cname (some (callocExpr countExpr))) .normal after ∧
      after.objects before.nextObject=some (zeroPrefixObject length 0) ∧
      after.environment.lookup cname=some (scalarPointer pointerId (.pointer .u64)) ∧
      Slot after pointerId before.scope (.pointer .u64) (.pointer (wordPointer before.nextObject 0)) ∧
      Frame before.nextObject before after [] ∧ after.scope=before.scope ∧
      after.environment=(cname,scalarPointer pointerId (.pointer .u64))::before.environment ∧
      before.nextObject<pointerId ∧ pointerId<after.nextObject := by
  obtain ⟨born,eval,raw,frame,environment,scope⟩:=calloc_success context absent memory well host byteFit countEval
  have storage:=ZeroFrame.pointer_storable before.nextObject
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists frame.well (.pointer .u64) cname _ storage
  have d:=declare_storable storage storage.converted declared
  have bound:=frame.well.objectIds _ _ raw
  refine ⟨after,born.nextObject,.declareSome eval declared,?_,?_,?_,?_,d.scope.trans scope,?_,bound,?_⟩
  · exact (d.outside _ (by omega)).trans raw
  · rw [d.environment]
    simp [List.lookup]
  · simpa only [scope] using d.slot
  · exact frame.trans (declare_frame before.nextObject [] frame.well frame.fresh declared)
  · rw [d.environment,environment]
  · rw [d.nextObject]
    omega

/-- The equally valid failure declaration returns a real initialized NULL slot.
No application buffer or desired result is postulated for allocation failure. -/
theorem calloc_null_birth {F : Type} (context : Context F) {before : State F}
    {countExpr : Expr} {length : Nat} (cname : String)
    (absent : findFunction context.program "calloc"=none) (memory : HasMemory context)
    (well : WellScoped before) (fit : length<2^64)
    (countEval : Eval context before countExpr (.integer (integer64 length)) before) :
    ∃after,Exec context before (.declare (.pointer .u64) cname (some (callocExpr countExpr))) .normal after ∧
      after.environment.lookup cname=some (scalarPointer before.nextObject (.pointer .u64)) ∧
      Slot after before.nextObject before.scope (.pointer .u64) .null ∧
      Frame before.nextObject before after [] := by
  have storage : Storable (.pointer .u64) .null := ⟨rfl,by decide,rfl⟩
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists well (.pointer .u64) cname .null storage
  have d:=declare_storable storage storage.converted declared
  refine ⟨after,.declareSome (calloc_failure context absent memory fit countEval) declared,?_,d.slot,
    declare_frame before.nextObject [] well (le_refl _) declared⟩
  rw [d.environment]
  simp [List.lookup]

#print axioms calloc_pointer_birth
#print axioms calloc_null_birth
end RH080Next.FFTPV.MainAllocation
