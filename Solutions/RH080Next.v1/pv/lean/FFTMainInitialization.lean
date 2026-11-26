/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainNullGuards
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource

def initializationPrefix : List Stmt:=allocationPrefix++guardPrefix++zeroPrefix

theorem actual_w4_initialization_prefix : (bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).take 12=initializationPrefix := by rfl
theorem actual_fap_initialization_prefix : (bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).take 12=initializationPrefix := by rfl

private theorem append_execution {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow}
    (first : ExecList context before xs .normal middle) (second : ExecList context middle ys flow after) :
    ExecList context before (xs++ys) flow after := by
  induction xs generalizing before with
  | nil=>cases first;exact second
  | cons x xs ih=>
    cases first with
    | cons head tail=>exact .cons head (ih tail)
    | abrupt head impossible=>exact False.elim (impossible rfl)

private theorem erase_future_writes {F : Type} {before after : State F} {cutoff : Nat} {writes : List Nat}
    (f : Frame cutoff before after writes) (future : ∀id∈writes,cutoff ≤ id) : Frame cutoff before after [] := by
  refine ⟨f.well,f.fresh,f.nextObject,f.nextScope,f.mode,f.foreign,?_⟩
  intro id old _
  apply f.outside id old
  intro written
  have bound:=future id written
  omega

theorem initialized_words {F : Type} {state : State F} {n nId owner : Nat} {objects ids : Role → Nat}
    (h : InitializedView state n nId owner objects ids [.work,.twiddle,.data,.output]) (r : Role) :
    WordArrayRep state (objects r) (length n r) (fun _=>0) := by
  have member : r∈[.work,.twiddle,.data,.output] := by cases r <;> simp
  simpa only [MemoryReady,if_pos member] using h.memory r

/-- Actual first12 source statements: four generic byte allocations, actual
NULL guards, and four complete zero_words calls. No initial typed buffer or
correct output is an assumption. This is the constructed successful branch;
whole-main all-execution failure classification remains a separate theorem. -/
theorem source_initialization {F : Type} (context : Context F) {before : State F}
    {n nId owner : Nat} (nLookup : before.environment.lookup "n"=some (scalarPointer nId .u64))
    (nSlot : Slot before nId owner .u64 (.integer (integer64 n)))
    (well : WellScoped before) (host : before.mode=.host) (scope : before.scope=owner)
    (small : n≤2^24) (absent : findFunction context.program "calloc"=none) (memory : HasMemory context)
    (selected : findFunction context.program "zero_words"=some zero_words_ast) :
    ∃after objects ids,ExecList context before initializationPrefix .normal after ∧
      InitializedView after n nId owner objects ids [.work,.twiddle,.data,.output] ∧
      (∀r,WordArrayRep after (objects r) (length n r) (fun _=>0)) ∧
      Frame before.nextObject before after [] ∧ (∀r,before.nextObject≤objects r) := by
  obtain ⟨allocated,objects,ids,allocatedRun,raw,allocFrame,future⟩:=
    four_allocations context nLookup nSlot well host scope small absent memory
  have initial:=raw.initialized
  have guards:=initial.all_guard_steps context
  obtain ⟨after,zeros,complete,zeroFrame⟩:=initial.all_zero_steps context small selected
  have allRun:=append_execution (append_execution allocatedRun guards.execution) zeros.execution
  have lowered:=lower_cutoff zeroFrame allocFrame.nextObject
  have erased : Frame before.nextObject allocated after [] := by
    apply erase_future_writes lowered
    intro id member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> exact future _
  exact ⟨after,objects,ids,allRun,complete,initialized_words complete,allocFrame.trans erased,future⟩

#print axioms actual_w4_initialization_prefix
#print axioms actual_fap_initialization_prefix
#print axioms source_initialization
end RH080Next.FFTPV.MainAllocation
