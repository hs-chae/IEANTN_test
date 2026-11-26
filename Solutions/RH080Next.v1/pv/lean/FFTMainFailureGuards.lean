import FFTMainFailureFour
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

def allocationFailureValue : Value := .integer (integer64 18446744073709551615)

theorem failure_return_flow {F : Type} (context : Context F) {before after : State F} {flow : Flow}
    (run : Exec context before failureReturn flow after) : flow=.returned allocationFailureValue := by
  cases run with
  | returnSome ev =>
    have expected : Eval context before (.literal (.integer 18446744073709551615 "ULL")) allocationFailureValue before :=
      .literal (.integer 18446744073709551615 "ULL") _ allocationFailureValue (by rfl)
    obtain ⟨rfl,_⟩:=PureDeterminism.eval_unique (by trivial) expected ev
    rfl

theorem free_statement_normal {F : Type} (context : Context F) {before after : State F}
    {flow : Flow} {cname : String} (absent : findFunction context.program "free"=none)
    (sound : MemorySound context) (actual : Exec context before (freeStatement cname) flow after) :
    flow=.normal := by
  cases actual with
  | expression _ => rfl
  | callTerminated _ called =>
    obtain ⟨operation,named,foreign⟩:=call_external_of_absent absent called
    have eq : operation=.free := by cases operation <;> simp_all [External.name]
    subst operation
    obtain ⟨value,result,_⟩:=sound _ _ _ _ _ (Or.inr rfl) foreign
    cases result

/-- Every completed failure-cleanup path returns UINT64_MAX, irrespective of
which earlier allocations succeeded. Generic free excludes process termination. -/
theorem cleanup_return_flow {F : Type} (context : Context F) {before after : State F}
    {flow : Flow} (names : List String) (absent : findFunction context.program "free"=none)
    (sound : MemorySound context)
    (actual : ExecList context before (names.map freeStatement++[failureReturn]) flow after) :
    flow=.returned allocationFailureValue := by
  induction names generalizing before with
  | nil =>
    cases actual with
    | cons head tail =>
      have impossible:=failure_return_flow context head
      cases impossible
    | abrupt head _ => exact failure_return_flow context head
  | cons cname names ih =>
    cases actual with
    | cons head tail => exact ih tail
    | abrupt head abrupt => exact False.elim (abrupt (free_statement_normal context absent sound head))

theorem failure_block_flow {F : Type} (context : Context F) {before after : State F}
    {flow : Flow} (r : Role) (absent : findFunction context.program "free"=none)
    (sound : MemorySound context)
    (actual : Exec context before (.block ((earlierNames r).map freeStatement++[failureReturn])) flow after) :
    flow=.returned allocationFailureValue := by
  cases actual with
  | block _ body _ => exact cleanup_return_flow context (earlierNames r) absent sound body

theorem NullableView.null_test {F : Type} (context : Context F) {state : State F}
    {n nId owner : Nat} {roles : List Role} {objects : Role → Option Nat} {ids : Role → Nat}
    (h : NullableView state n nId owner roles objects ids) (r : Role) (member : r∈roles) :
    Eval context state (nullTest r) (.integer (.boolean (objects r).isNone)) state := by
  have pointer : Eval context state (.variable (name r)) (nullablePointer (objects r)) state :=
    .variable (h.lookup r member) (h.slots r member).read
  refine .binaryLR pointer (.literal .nullPointer _ .null (by rfl)) ?_
  cases objects r <;> rfl

theorem NullableView.guard_cases {F : Type} (context : Context F) {before after : State F}
    {n nId owner : Nat} {roles : List Role} {objects : Role → Option Nat} {ids : Role → Nat}
    {flow : Flow} (h : NullableView before n nId owner roles objects ids) (r : Role) (member : r∈roles)
    (absent : findFunction context.program "free"=none) (sound : MemorySound context)
    (actual : Exec context before (nullGuard r) flow after) :
    flow=.returned allocationFailureValue ∨ (flow=.normal ∧ after=before ∧ objects r≠none) := by
  have expected:=h.null_test context r member
  cases actual with
  | ifTrue ev truth body =>
    obtain ⟨valueEq,stateEq⟩:=PureDeterminism.eval_unique (by trivial) expected ev
    exact Or.inl (failure_block_flow context r absent sound body)
  | ifFalse ev truth =>
    obtain ⟨valueEq,stateEq⟩:=PureDeterminism.eval_unique (by trivial) expected ev
    refine Or.inr ⟨rfl,stateEq.symm,?_⟩
    intro eq
    rw [←valueEq,eq] at truth
    cases truth

theorem NullableView.guards_cases {F : Type} (context : Context F) {before after : State F}
    {n nId owner : Nat} {roles : List Role} {objects : Role → Option Nat} {ids : Role → Nat}
    {flow : Flow} (h : NullableView before n nId owner roles objects ids) (tests : List Role)
    (members : ∀r∈tests,r∈roles) (absent : findFunction context.program "free"=none)
    (sound : MemorySound context) (actual : ExecList context before (tests.map nullGuard) flow after) :
    flow=.returned allocationFailureValue ∨
      (flow=.normal ∧ after=before ∧ ∀r∈tests,objects r≠none) := by
  induction tests generalizing after flow with
  | nil => cases actual;exact Or.inr ⟨rfl,rfl,by simp⟩
  | cons r tests ih =>
    cases actual with
    | cons head tail =>
      rcases h.guard_cases context r (members r (by simp)) absent sound head with failed|normal
      · cases failed
      · rcases normal with ⟨_,middleEq,nonnull⟩
        subst middleEq
        rcases ih (fun s member=>members s (by simp [member])) tail with failed|normal
        · exact Or.inl failed
        · exact Or.inr ⟨normal.1,normal.2.1,by intro s member;rcases List.mem_cons.mp member with rfl|rest;exact nonnull;exact normal.2.2 s rest⟩
    | abrupt head abrupt =>
      rcases h.guard_cases context r (members r (by simp)) absent sound head with failed|normal
      · exact Or.inl failed
      · exact False.elim (abrupt normal.1)

/-- Every execution of the four actual NULL guards either returns the source
sentinel or leaves the same actual state and establishes its nonNULL raw view. -/
theorem every_guard_prefix {F : Type} (context : Context F) {before after : State F}
    {n nId owner : Nat} {objects : Role → Option Nat} {ids : Role → Nat} {flow : Flow}
    (h : NullableView before n nId owner [.output,.work,.twiddle,.data] objects ids)
    (absent : findFunction context.program "free"=none) (sound : MemorySound context)
    (actual : ExecList context before guardPrefix flow after) :
    flow=.returned allocationFailureValue ∨ (flow=.normal ∧ after=before ∧
      View before n nId owner [.output,.work,.twiddle,.data] (fun r=>(objects r).getD 0) ids) := by
  rcases h.guards_cases context [.data,.twiddle,.work,.output] (by intro r _;exact all_roles r) absent sound actual with failed|normal
  · exact Or.inl failed
  · refine Or.inr ⟨normal.1,normal.2.1,h.nonnull_view ?_⟩
    intro r _
    exact normal.2.2 r (by cases r <;> simp)

#print axioms cleanup_return_flow
#print axioms every_guard_prefix
end RH080Next.FFTPV.MainAllocation
