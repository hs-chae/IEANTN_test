/- Universal operational main/printf association, including all permitted
argument orders and all modeled allocation/I/O failure choices. -/
import FFTMainIOExecution
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.MainIO
open GoldbachDirect GoldbachDirect.Semantics WordArrays MainAllocation MainSuffix SourceLocals

theorem main_parameters (p : InputLoader.Profile) : (SourceOutput.sourceMain p).parameters=[] := by
  cases p <;> rfl

theorem main_result (p : InputLoader.Profile) : (SourceOutput.sourceMain p).result=.int := by
  cases p <;> rfl

theorem actual_printf_call (p : InputLoader.Profile)
    {values : List Value} {before after : State IOState} {result : CallResult}
    (actual : Call (ioContext p.program) "printf" values before result after) :
    PrintfCall values before result after := by
  obtain ⟨operation,named,api⟩:=call_external_of_absent (by cases p <;> rfl) actual
  have operationEq : operation=.printf := by cases operation <;> simp_all [External.name]
  subst operation
  exact printf_cases api

theorem printf_statement (p : InputLoader.Profile)
    {before after : State IOState} {flow : Flow}
    (actual : Exec (ioContext p.program) before (.expression (.call "printf" (printfExpressions p))) flow after) :
    flow=.normal ∧ ∃values middle result,
      Args (ioContext p.program) before (printfExpressions p) values middle ∧
      PrintfCall values middle (.value result) after := by
  cases actual with
  | expression evaluated =>
    cases evaluated with
    | load place read => cases place
    | call arguments called => exact ⟨rfl,_,_,_,arguments,actual_printf_call p called⟩
  | callTerminated arguments called => cases actual_printf_call p called

theorem list_association (p : InputLoader.Profile)
    {before after : State IOState} {flow : Flow}
    (actual : ExecList (ioContext p.program) before (mainStatements p) flow after) :
    flow=.returned zero ∧ ∃values middle result,
      Args (ioContext p.program) before (printfExpressions p) values middle ∧
      PrintfCall values middle (.value result) after := by
  cases actual with
  | cons first rest =>
    obtain ⟨_,values,middle,result,args,api⟩:=printf_statement p first
    cases rest with
    | cons first rest => cases first
    | abrupt first abrupt =>
      cases first with
      | returnSome evaluated =>
        obtain ⟨rfl,rfl⟩:=literal_exact (by rfl : (Literal.integer 0 "").value=some zero) evaluated
        exact ⟨rfl,values,middle,result,args,api⟩
  | abrupt first abrupt => exact False.elim (abrupt (printf_statement p first).1)

theorem body_association (p : InputLoader.Profile)
    {before after : State IOState} {flow : Flow}
    (actual : Body (ioContext p.program) (mainStatements p) before (mainStatements p) flow after) :
    flow=.returned zero ∧ ∃values middle result,
      Args (ioContext p.program) before (printfExpressions p) values middle ∧
      PrintfCall values middle (.value result) after := by
  cases actual with
  | finish actual _ => exact list_association p actual
  | jump actual _ _ => cases (list_association p actual).1

/-- Every complete actual main Call returns zero and passes the actual nested
norm result to printf. Allocation failure requests UINT64_MAX. All other
requests are exactly the source-proved numerical answer. Printf may succeed
or may return a negative int after writing only a prefix. -/
theorem every_main_call (p : InputLoader.Profile) (certificate : MainCertificate.Certificate p)
    (initial : IOState) {after : State IOState} {result : CallResult}
    (actual : Call (ioContext p.program) "main" [] (caller initial) result after) :
    result=.value zero ∧ ∃out normAfter printfAfter printfResult,
      out<2^64 ∧ (out=AnswerSource.sentinel ∨ out=normAnswer p certificate) ∧
      Call (ioContext p.program) (failureSourceFunction (isFap p)).name
        [.integer (integer64 p.grid)] (mainEntry initial) (.value (.integer (integer64 out))) normAfter ∧
      PrintfCall [.string "%llu\n",.integer (integer64 out)] normAfter (.value printfResult) printfAfter ∧
      after=mainFinish printfAfter initial := by
  cases actual with
  | external absent _ _ =>
    change findFunction p.program "main"=none at absent
    rw [SourceOutput.actual_main_selected p] at absent;cases absent
  | internal selected shape parameters body converted finished =>
    change findFunction p.program "main"=some _ at selected
    rw [SourceOutput.actual_main_selected p] at selected
    cases Option.some.inj selected
    have statementsEq:=Stmt.block.inj (shape.symm.trans (main_body p))
    subst_vars
    have enteredEq:=parameters
    rw [main_parameters p] at enteredEq
    dsimp only [bindParameters] at enteredEq
    cases Option.some.inj enteredEq
    obtain ⟨flowEq,values,normAfter,printfResult,args,api⟩:=body_association p body
    cases flowEq
    rw [main_result p] at converted
    change some zero=some _ at converted
    cases Option.some.inj converted
    obtain ⟨out,rfl,fit,value,called⟩:=every_printf_arguments p certificate (mainEntry_well initial) rfl args
    exact ⟨rfl,out,normAfter,_,printfResult,fit,value,called,api,rfl⟩
  | internalVoid selected _ void _ _ _ =>
    change findFunction p.program "main"=some _ at selected
    rw [SourceOutput.actual_main_selected p] at selected
    cases Option.some.inj selected
    rw [main_result p] at void
    cases void
  | internalTerminated selected shape parameters body =>
    change findFunction p.program "main"=some _ at selected
    rw [SourceOutput.actual_main_selected p] at selected
    cases Option.some.inj selected
    have statementsEq:=Stmt.block.inj (shape.symm.trans (main_body p))
    subst_vars
    cases (body_association p body).1

end RH080Next.FFTPV.MainIO
