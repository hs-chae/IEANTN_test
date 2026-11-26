/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSourceNormSuffix
import FFTMainCallResult
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

theorem normAnswer_fits (p : InputLoader.Profile) (certificate : MainCertificate.Certificate p) :
    normAnswer p certificate<2^64 := MainFinish.finishValue_fits _ _ _ _

theorem selected_norm {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) :
    findFunction context.program (failureSourceFunction (isFap p)).name=some (failureSourceFunction (isFap p)) := by
  rw [pinned];cases p <;> rfl

theorem calloc_absent {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) : findFunction context.program "calloc"=none := by rw [pinned];cases p <;> rfl

theorem free_absent {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) : findFunction context.program "free"=none := by rw [pinned];cases p <;> rfl

/-- Every actual whole norm Call either follows the genuine allocation-failure
sentinel branch or returns the proved source-derived answer. There is no
application suffix-correctness or successful-execution premise. -/
theorem every_norm_call {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) (certificate : MainCertificate.Certificate p)
    (has : HasMemory context) (sound : MemorySound context)
    {caller after : State F} {result : CallResult}
    (well : WellScoped caller) (host : caller.mode=.host)
    (actual : Call context (failureSourceFunction (isFap p)).name [.integer (integer64 p.grid)] caller result after) :
    result=.value allocationFailureValue ∨ result=.value (.integer (integer64 (normAnswer p certificate))) := by
  apply norm_call_result_of_suffix context (isFap p) (selected_norm context p pinned) well host
    (by cases p <;> decide) (calloc_absent context p pinned) (free_absent context p pinned) sound
    (normAnswer_fits p certificate) ?_ actual
  intro allocated objects ids raw middle flow run
  exact every_norm_suffix context p pinned certificate has sound raw run

/-- Construct the actual complete norm Call from an arbitrary well-scoped host
caller, including parameter binding, four real raw allocations, NULL checks,
all application computations, all releases and the function-scope exit.
The separate universal theorem above also covers all allocation failures. -/
theorem norm_call_exists {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) (certificate : MainCertificate.Certificate p)
    (has : HasMemory context) (sound : MemorySound context)
    (caller : State F) (well : WellScoped caller) (host : caller.mode=.host) :
    ∃after,Call context (failureSourceFunction (isFap p)).name [.integer (integer64 p.grid)] caller
      (.value (.integer (integer64 (normAnswer p certificate)))) after := by
  have small : p.grid≤2^24 := by cases p <;> decide
  obtain ⟨entered,parameters,lookup,slot,we,enteredScope,mode,_,_,_⟩ :=
    bind_norm_parameter p.grid well (by have h:=small;omega)
  obtain ⟨allocated,objects,ids,allocRun,raw,_,_⟩ := four_allocations context lookup slot we
    (mode.trans host) enteredScope small (calloc_absent context p pinned) has
  have guards := raw.initialized.all_guard_steps context
  obtain ⟨middle,suffix,_⟩ := norm_suffix_total context p pinned certificate has sound raw
  have fullRun : ExecList context entered (bodyItems (failureSourceFunction (isFap p)))
      (.returned (.integer (integer64 (normAnswer p certificate)))) middle := by
    have run := MainFinish.append_run allocRun (MainFinish.append_run guards.execution suffix.execution)
    have shape : bodyItems (failureSourceFunction (isFap p))=
        allocationPrefix++(guardPrefix++normSuccessSuffix (failureSourceFunction (isFap p))) := by cases p <;> rfl
    rw [shape]
    exact run
  let after : State F := {middle.leaveScope caller.nextScope caller.environment with scope:=caller.scope}
  refine ⟨after,?_⟩
  have bodyShape : (failureSourceFunction (isFap p)).body=.block (bodyItems (failureSourceFunction (isFap p))) := by cases p <;> rfl
  have params : bindParameters {caller.enterScope with environment:=[]} (failureSourceFunction (isFap p)).parameters
      [.integer (integer64 p.grid)]=some entered := by cases p <;> exact parameters
  apply Call.internal (function:=failureSourceFunction (isFap p)) (entered:=entered) (middle:=middle)
    (selected_norm context p pinned) bodyShape params
  · exact Body.finish fullRun (by intro label impossible;cases impossible)
  · have resultType : (failureSourceFunction (isFap p)).result=.u64 := by cases p <;> rfl
    rw [resultType]
    exact convert64 (normAnswer p certificate) (normAnswer_fits p certificate)
  · simp only [after,enteredScope]

/-- The verified successful-output interpretation has no unverified application
correctness premise; the sole success hypothesis excludes the real C sentinel. -/
theorem successful_norm_call {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) (certificate : MainCertificate.Certificate p)
    (has : HasMemory context) (sound : MemorySound context)
    {caller after : State F} {result : CallResult}
    (well : WellScoped caller) (host : caller.mode=.host)
    (actual : Call context (failureSourceFunction (isFap p)).name [.integer (integer64 p.grid)] caller result after)
    (success : result≠.value allocationFailureValue) : result=.value (.integer (integer64 (normAnswer p certificate))) :=
  (every_norm_call context p pinned certificate has sound well host actual).resolve_left success

#print axioms normAnswer_fits
#print axioms every_norm_call
#print axioms norm_call_exists
#print axioms successful_norm_call
end RH080Next.FFTPV.MainSuffix
