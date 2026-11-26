/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainAllocationView
import FFTRecursiveAST
import FapFFTRecursiveAST
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

def allocationPrefix : List Stmt := [.data,.twiddle,.work,.output].map statement

def bodyItems (function : GoldbachDirect.Function) : List Stmt :=
  match function.body with | .block statements=>statements | _=>[]

theorem actual_w4_allocation_prefix : (bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).take 4=allocationPrefix := by rfl

theorem actual_fap_allocation_prefix : (bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).take 4=allocationPrefix := by rfl

theorem lower_cutoff {F : Type} {before after : State F} {cutoff earlier : Nat} {writes : List Nat}
    (frame : Frame cutoff before after writes) (bound : earlier≤cutoff) : Frame earlier before after writes :=
  ⟨frame.well,bound.trans frame.fresh,frame.nextObject,frame.nextScope,frame.mode,frame.foreign,
    fun id old absent=>frame.outside id (old.trans_le bound) absent⟩

/-- Actual four C calloc/declaration instructions in their source order.
This theorem constructs their success branch from generic allocation semantics;
NULL branches remain present in calloc_failure/calloc_null_birth. No typed
array initialization or application numerical output is assumed. -/
theorem four_allocations {F : Type} (context : Context F) {before : State F}
    {n nId owner : Nat} (nLookup : before.environment.lookup "n"=some (scalarPointer nId .u64))
    (nSlot : Slot before nId owner .u64 (.integer (integer64 n)))
    (well : WellScoped before) (host : before.mode=.host) (scope : before.scope=owner)
    (small : n≤2^24) (absent : findFunction context.program "calloc"=none) (memory : HasMemory context) :
    ∃after objects ids,ExecList context before allocationPrefix .normal after ∧
      View after n nId owner [.output,.work,.twiddle,.data] objects ids ∧
      Frame before.nextObject before after [] ∧ (∀r,before.nextObject≤objects r) := by
  have h0:=View.initial nLookup nSlot well host scope
  obtain ⟨s1,id1,exec1,h1,f1⟩:=h0.birth context .data small (by simp) absent memory
  obtain ⟨s2,id2,exec2,h2,f2⟩:=h1.birth context .twiddle small (by simp) absent memory
  obtain ⟨s3,id3,exec3,h3,f3⟩:=h2.birth context .work small (by simp) absent memory
  obtain ⟨after,id4,exec4,h4,f4⟩:=h3.birth context .output small (by simp) absent memory
  have c2:=f1.trans (lower_cutoff f2 f1.nextObject)
  have c3:=c2.trans (lower_cutoff f3 c2.nextObject)
  refine ⟨after,_,_,.cons exec1 (.cons exec2 (.cons exec3 (.cons exec4 .nil))),h4,
    c3.trans (lower_cutoff f4 c3.nextObject),?_⟩
  have b1:=f1.nextObject
  have b2:=c2.nextObject
  have b3:=c3.nextObject
  intro r
  cases r <;> simp only [Function.update_apply] <;> simp <;> omega

#print axioms actual_w4_allocation_prefix
#print axioms actual_fap_allocation_prefix
#print axioms four_allocations
end RH080Next.FFTPV.MainAllocation
