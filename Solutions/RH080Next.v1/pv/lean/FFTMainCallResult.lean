/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainFailureCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

/-- Operational composition only: the separately proved application suffix
discharges `suffixCorrect`.  It is a mathematical helper premise, never part
of the generic allocator/runtime contract.  Every actual norm Call is covered,
including all independent calloc choices and the termination constructors. -/
theorem norm_call_result_of_suffix {F : Type} (context : Context F) (fap : Bool)
    {caller after : State F} {n answer : Nat} {result : CallResult}
    (selected : findFunction context.program (failureSourceFunction fap).name=
      some (failureSourceFunction fap))
    (well : WellScoped caller) (host : caller.mode=.host) (small : n≤2^24)
    (callocAbsent : findFunction context.program "calloc"=none)
    (freeAbsent : findFunction context.program "free"=none) (sound : MemorySound context)
    (fits : answer<2^64)
    (suffixCorrect : ∀allocated objects ids,
      View allocated n caller.nextObject caller.nextScope [.output,.work,.twiddle,.data] objects ids →
      ∀middle flow,ExecList context allocated (normSuccessSuffix (failureSourceFunction fap)) flow middle →
        flow=.returned (.integer (integer64 answer)))
    (actual : Call context (failureSourceFunction fap).name [.integer (integer64 n)] caller result after) :
    result=.value allocationFailureValue ∨ result=.value (.integer (integer64 answer)) := by
  rcases every_norm_call_prefix context fap selected well host small callocAbsent freeAbsent sound actual
      with failed | success
  · exact Or.inl failed
  · obtain ⟨allocated,middle,objects,ids,flow,view,_,_,run,completion⟩:=success
    have exactFlow:=suffixCorrect allocated objects ids view middle flow run
    rw [exactFlow] at completion
    rcases completion with returned | terminated
    · obtain ⟨value,output,eq,rfl,converted,_⟩:=returned
      cases eq
      have outputEq : output=.integer (integer64 answer) :=
        Option.some.inj (converted.symm.trans (convert64 answer fits))
      exact Or.inr (congrArg CallResult.value outputEq)
    · obtain ⟨status,impossible,_,_⟩:=terminated
      cases impossible

/-- A non-sentinel physical result, once associated with the formal Call by
the documented compiler/runtime boundary, is the proved application answer. -/
theorem norm_call_success_of_suffix {F : Type} (context : Context F) (fap : Bool)
    {caller after : State F} {n answer : Nat} {result : CallResult}
    (selected : findFunction context.program (failureSourceFunction fap).name=
      some (failureSourceFunction fap))
    (well : WellScoped caller) (host : caller.mode=.host) (small : n≤2^24)
    (callocAbsent : findFunction context.program "calloc"=none)
    (freeAbsent : findFunction context.program "free"=none) (sound : MemorySound context)
    (fits : answer<2^64)
    (suffixCorrect : ∀allocated objects ids,
      View allocated n caller.nextObject caller.nextScope [.output,.work,.twiddle,.data] objects ids →
      ∀middle flow,ExecList context allocated (normSuccessSuffix (failureSourceFunction fap)) flow middle →
        flow=.returned (.integer (integer64 answer)))
    (actual : Call context (failureSourceFunction fap).name [.integer (integer64 n)] caller result after)
    (success : result≠.value allocationFailureValue) : result=.value (.integer (integer64 answer)) := by
  exact (norm_call_result_of_suffix context fap selected well host small callocAbsent freeAbsent sound
    fits suffixCorrect actual).resolve_left success

#print axioms norm_call_result_of_suffix
#print axioms norm_call_success_of_suffix
end RH080Next.FFTPV.MainAllocation
