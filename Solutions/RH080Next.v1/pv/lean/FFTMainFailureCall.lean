import FFTMainFailurePrefix
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

def failureSourceFunction (fap : Bool) : GoldbachDirect.Function :=
  if fap then FapFFTRecursivePV.fap_recursive_norm_upper_ast else FFTRecursivePV.w4_recursive_norm_upper_ast

theorem failure_source_body (fap : Bool) : (failureSourceFunction fap).body=
    .block (allocationPrefix++(guardPrefix++normSuccessSuffix (failureSourceFunction fap))) := by
  cases fap <;> rfl

theorem failure_source_parameters (fap : Bool) : (failureSourceFunction fap).parameters=[(.u64,"n")] := by
  cases fap <;> rfl

theorem failure_source_result (fap : Bool) : (failureSourceFunction fap).result=.u64 := by
  cases fap <;> rfl

theorem failure_source_no_labels (fap : Bool) (label : String) :
    labelTail label (allocationPrefix++(guardPrefix++normSuccessSuffix (failureSourceFunction fap)))=none := by
  cases fap <;> rfl

theorem no_labels_body_execution {F : Type} {context : Context F} {whole statements : List Stmt}
    {before after : State F} {flow : Flow} (noLabels : ∀label,labelTail label whole=none)
    (actual : Body context whole before statements flow after) :
    ExecList context before statements flow after := by
  cases actual with
  | finish run _=>exact run
  | jump _ target _=>rw [noLabels] at target;cases target

/-- Actual returned-value conversion and actual caller scope restoration, or
actual process termination. This records operational witnesses, never a desired output. -/
def SourceCompletion {F : Type} (caller : State F) (result : CallResult) (after : State F)
    (flow : Flow) (middle : State F) : Prop :=
  (∃value output,flow=.returned value ∧ result=.value output ∧ Value.convert .u64 value=some output ∧
    after={middle.leaveScope caller.nextScope caller.environment with scope:=caller.scope}) ∨
  (∃status,flow=.terminated status ∧ result=.terminated status ∧ after=middle)

private theorem completion_of_sentinel {F : Type} {caller after middle : State F}
    {result : CallResult} (completion : SourceCompletion caller result after (.returned allocationFailureValue) middle) :
    result=.value allocationFailureValue := by
  rcases completion with returned|terminated
  · obtain ⟨value,output,equal,rfl,converted,finished⟩:=returned
    cases equal
    have eq : output=allocationFailureValue := Option.some.inj (converted.symm.trans (by rfl))
    cases eq
    rfl
  · obtain ⟨status,impossible,_,_⟩:=terminated
    cases impossible

private theorem entered_call_prefix {F : Type} (context : Context F) {caller entered after middle : State F}
    {n : Nat} {result : CallResult} {flow : Flow} (fap : Bool)
    (lookup : entered.environment.lookup "n"=some (scalarPointer caller.nextObject .u64))
    (slot : Slot entered caller.nextObject caller.nextScope .u64 (.integer (integer64 n)))
    (well : WellScoped entered) (host : entered.mode=.host) (scope : entered.scope=caller.nextScope)
    (parameterFrame : Frame caller.nextObject caller.enterScope entered [])
    (nextObject : entered.nextObject=caller.nextObject+1)
    (small : n≤2^24) (callocAbsent : findFunction context.program "calloc"=none)
    (freeAbsent : findFunction context.program "free"=none) (sound : MemorySound context)
    (actual : ExecList context entered (allocationPrefix++(guardPrefix++normSuccessSuffix (failureSourceFunction fap))) flow middle)
    (completion : SourceCompletion caller result after flow middle) :
    result=.value allocationFailureValue ∨ ∃allocated objects ids,
      View allocated n caller.nextObject caller.nextScope [.output,.work,.twiddle,.data] objects ids ∧
      Frame caller.nextObject caller.enterScope allocated [] ∧
      (∀r,caller.nextObject < objects r) ∧
      ExecList context allocated (normSuccessSuffix (failureSourceFunction fap)) flow middle ∧
      SourceCompletion caller result after flow middle := by
  rcases every_norm_prefix context _ lookup slot well host scope small callocAbsent freeAbsent sound actual with failed|success
  · rw [failed] at completion
    exact Or.inl (completion_of_sentinel completion)
  · obtain ⟨allocated,objects,ids,view,frame,fresh,suffix⟩:=success
    refine Or.inr ⟨allocated,objects,ids,view,
      parameterFrame.trans (lower_cutoff frame parameterFrame.nextObject),?_,suffix,completion⟩
    intro r
    have bound:=fresh r
    rw [nextObject] at bound
    omega

/-- Every actual norm-function Call is classified, including every independent
calloc failure. The nonNULL branch uses this Call's real parameter binding,
real raw memory, exact suffix execution, return conversion and scope finish.
Termination remains explicit for the subsequent verified suffix to discharge. -/
theorem every_norm_call_prefix {F : Type} (context : Context F) (fap : Bool)
    {caller after : State F} {n : Nat} {result : CallResult}
    (selected : findFunction context.program (failureSourceFunction fap).name=some (failureSourceFunction fap))
    (well : WellScoped caller) (host : caller.mode=.host) (small : n≤2^24)
    (callocAbsent : findFunction context.program "calloc"=none)
    (freeAbsent : findFunction context.program "free"=none) (sound : MemorySound context)
    (actual : Call context (failureSourceFunction fap).name [.integer (integer64 n)] caller result after) :
    result=.value allocationFailureValue ∨ ∃allocated middle objects ids flow,
      View allocated n caller.nextObject caller.nextScope [.output,.work,.twiddle,.data] objects ids ∧
      Frame caller.nextObject caller.enterScope allocated [] ∧
      (∀r,caller.nextObject < objects r) ∧
      ExecList context allocated (normSuccessSuffix (failureSourceFunction fap)) flow middle ∧
      SourceCompletion caller result after flow middle := by
  obtain ⟨entered,bound,lookup,slot,we,scope,mode,no,ns,parameterFrame⟩:=bind_norm_parameter n well (by omega)
  cases actual with
  | external absent _ _=>rw [selected] at absent;cases absent
  | internal chosen shape parameters body converted finished=>
    have functionEq:=Option.some.inj (selected.symm.trans chosen)
    subst_vars
    have statementsEq:=Stmt.block.inj ((failure_source_body fap).symm.trans shape)
    subst_vars
    rw [failure_source_parameters] at parameters
    have enteredEq:=Option.some.inj (bound.symm.trans parameters)
    subst_vars
    rw [failure_source_result] at converted
    have run:=no_labels_body_execution (failure_source_no_labels fap) body
    rcases entered_call_prefix context fap lookup slot we (mode.trans host) scope parameterFrame no small
      callocAbsent freeAbsent sound run (Or.inl ⟨_,_,rfl,rfl,converted,rfl⟩) with failed|success
    · exact Or.inl failed
    · obtain ⟨allocated,objects,ids,view,frame,fresh,suffix,complete⟩:=success
      exact Or.inr ⟨allocated,_,objects,ids,_,view,frame,fresh,suffix,by simpa only [scope] using complete⟩
  | internalVoid chosen shape void parameters body finished=>
    have functionEq:=Option.some.inj (selected.symm.trans chosen)
    subst_vars
    rw [failure_source_result] at void
    cases void
  | internalTerminated chosen shape parameters body=>
    have functionEq:=Option.some.inj (selected.symm.trans chosen)
    subst_vars
    have statementsEq:=Stmt.block.inj ((failure_source_body fap).symm.trans shape)
    subst_vars
    rw [failure_source_parameters] at parameters
    have enteredEq:=Option.some.inj (bound.symm.trans parameters)
    subst_vars
    have run:=no_labels_body_execution (failure_source_no_labels fap) body
    rcases entered_call_prefix context fap lookup slot we (mode.trans host) scope parameterFrame no small
      callocAbsent freeAbsent sound run (Or.inr ⟨_,rfl,rfl,rfl⟩) with failed|success
    · exact Or.inl failed
    · obtain ⟨allocated,objects,ids,view,frame,fresh,suffix,complete⟩:=success
      exact Or.inr ⟨allocated,_,objects,ids,_,view,frame,fresh,suffix,complete⟩

#print axioms every_norm_call_prefix
end RH080Next.FFTPV.MainAllocation
