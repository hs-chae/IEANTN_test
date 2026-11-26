import FFTMainFailureGuards
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

theorem execution_append_cases {F : Type} {context : Context F}
    {before after : State F} {flow : Flow} (xs suffix : List Stmt)
    (actual : ExecList context before (xs++suffix) flow after) :
    (∃middle,ExecList context before xs .normal middle ∧ ExecList context middle suffix flow after) ∨
      (flow≠.normal ∧ ExecList context before xs flow after) := by
  induction xs generalizing before with
  | nil => exact Or.inl ⟨before,.nil,actual⟩
  | cons head xs ih =>
    cases actual with
    | cons first rest =>
      rcases ih rest with normal|abrupt
      · obtain ⟨middle,firstPart,secondPart⟩:=normal
        exact Or.inl ⟨middle,.cons first firstPart,secondPart⟩
      · exact Or.inr ⟨abrupt.1,.cons first abrupt.2⟩
    | abrupt first abrupt =>exact Or.inr ⟨abrupt,.abrupt first abrupt⟩

/-- Any execution of the actual source allocation/guard prefix and arbitrary
following source statements either returns UINT64_MAX or reaches its actual
fresh nonNULL raw arrays and then executes the following source statements.
This quantifies over every allocator choice and every completed result. -/
theorem every_norm_prefix {F : Type} (context : Context F) {before after : State F}
    {n nId owner : Nat} {flow : Flow} (suffix : List Stmt)
    (nLookup : before.environment.lookup "n"=some (scalarPointer nId .u64))
    (nSlot : Slot before nId owner .u64 (.integer (integer64 n)))
    (well : WellScoped before) (host : before.mode=.host) (scope : before.scope=owner)
    (small : n≤2^24) (callocAbsent : findFunction context.program "calloc"=none)
    (freeAbsent : findFunction context.program "free"=none) (sound : MemorySound context)
    (actual : ExecList context before (allocationPrefix++(guardPrefix++suffix)) flow after) :
    flow=.returned allocationFailureValue ∨ ∃allocated objects ids,
      View allocated n nId owner [.output,.work,.twiddle,.data] objects ids ∧
      Frame before.nextObject before allocated [] ∧
      (∀r,before.nextObject ≤ objects r) ∧ ExecList context allocated suffix flow after := by
  rcases execution_append_cases allocationPrefix (guardPrefix++suffix) actual with normal|abrupt
  · obtain ⟨allocated,prefixRun,restRun⟩:=normal
    obtain ⟨_,nullable,ids,view,frame,fresh⟩:=every_four_allocations context nLookup nSlot well host scope small callocAbsent sound prefixRun
    rcases execution_append_cases guardPrefix suffix restRun with guardsNormal|guardsAbrupt
    · obtain ⟨guarded,guardsRun,suffixRun⟩:=guardsNormal
      rcases view.guards_cases context [.data,.twiddle,.work,.output]
        (by intro r _;exact all_roles r) freeAbsent sound guardsRun with failed|passed
      · cases failed
      · have allNonnull : ∀r,nullable r≠none := fun r=>passed.2.2 r (by cases r <;> simp)
        refine Or.inr ⟨allocated,fun r=>(nullable r).getD 0,ids,
          view.nonnull_view (fun r _=>allNonnull r),frame,?_,?_⟩
        · intro r
          have someId : nullable r=some ((nullable r).getD 0) := by
            cases eq:nullable r with
            | none=>exact False.elim (allNonnull r eq)
            | some id=>rfl
          exact fresh r _ someId
        · simpa only [passed.2.1] using suffixRun
    · rcases view.guards_cases context [.data,.twiddle,.work,.output]
        (by intro r _;exact all_roles r) freeAbsent sound guardsAbrupt.2 with failed|passed
      · exact Or.inl failed
      · exact False.elim (guardsAbrupt.1 passed.1)
  · have normal:=(every_four_allocations context nLookup nSlot well host scope small callocAbsent sound abrupt.2).1
    exact False.elim (abrupt.1 normal)

def normSuccessSuffix (function : GoldbachDirect.Function) : List Stmt := (bodyItems function).drop 8

theorem actual_w4_allocation_guards : bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast=
    allocationPrefix++(guardPrefix++normSuccessSuffix FFTRecursivePV.w4_recursive_norm_upper_ast) := by rfl

theorem actual_fap_allocation_guards : bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast=
    allocationPrefix++(guardPrefix++normSuccessSuffix FapFFTRecursivePV.fap_recursive_norm_upper_ast) := by rfl

/-- Direct actual-w4 source-body specialization, without a successful-allocation premise. -/
theorem every_w4_norm_prefix {F : Type} (context : Context F) {before after : State F}
    {n nId owner : Nat} {flow : Flow}
    (nLookup : before.environment.lookup "n"=some (scalarPointer nId .u64))
    (nSlot : Slot before nId owner .u64 (.integer (integer64 n)))
    (well : WellScoped before) (host : before.mode=.host) (scope : before.scope=owner)
    (small : n≤2^24) (callocAbsent : findFunction context.program "calloc"=none)
    (freeAbsent : findFunction context.program "free"=none) (sound : MemorySound context)
    (actual : ExecList context before (bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast) flow after) :
    flow=.returned allocationFailureValue ∨ ∃allocated objects ids,
      View allocated n nId owner [.output,.work,.twiddle,.data] objects ids ∧
      Frame before.nextObject before allocated [] ∧
      (∀r,before.nextObject ≤ objects r) ∧
      ExecList context allocated (normSuccessSuffix FFTRecursivePV.w4_recursive_norm_upper_ast) flow after := by
  rw [actual_w4_allocation_guards] at actual
  exact every_norm_prefix context _ nLookup nSlot well host scope small callocAbsent freeAbsent sound actual

theorem every_fap_norm_prefix {F : Type} (context : Context F) {before after : State F}
    {n nId owner : Nat} {flow : Flow}
    (nLookup : before.environment.lookup "n"=some (scalarPointer nId .u64))
    (nSlot : Slot before nId owner .u64 (.integer (integer64 n)))
    (well : WellScoped before) (host : before.mode=.host) (scope : before.scope=owner)
    (small : n≤2^24) (callocAbsent : findFunction context.program "calloc"=none)
    (freeAbsent : findFunction context.program "free"=none) (sound : MemorySound context)
    (actual : ExecList context before (bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast) flow after) :
    flow=.returned allocationFailureValue ∨ ∃allocated objects ids,
      View allocated n nId owner [.output,.work,.twiddle,.data] objects ids ∧
      Frame before.nextObject before allocated [] ∧
      (∀r,before.nextObject ≤ objects r) ∧
      ExecList context allocated (normSuccessSuffix FapFFTRecursivePV.fap_recursive_norm_upper_ast) flow after := by
  rw [actual_fap_allocation_guards] at actual
  exact every_norm_prefix context _ nLookup nSlot well host scope small callocAbsent freeAbsent sound actual

#print axioms every_norm_prefix
#print axioms every_w4_norm_prefix
#print axioms every_fap_norm_prefix
end RH080Next.FFTPV.MainAllocation
