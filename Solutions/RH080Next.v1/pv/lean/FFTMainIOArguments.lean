/- Actual printf operands, including both permitted argument orders. -/
import FFTMainIOContract
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainIO
open GoldbachDirect GoldbachDirect.Semantics WordArrays MainAllocation MainSuffix SourceLocals

theorem literal_exact {F : Type} {context : Context F} {before after : State F}
    {literal : Literal} {value expected : Value}
    (valid : literal.value=some expected)
    (run : Eval context before (.literal literal) value after) : value=expected ∧ after=before :=
  PureDeterminism.eval_unique (by trivial) run (.literal literal before expected valid)

/-- The first operand is a pure literal, while the second may be stateful.
Every permitted evaluation order produces the same source-position pairing. -/
theorem two_arguments {F : Type} {context : Context F} {before after : State F}
    {literal : Literal} {expected : Value} {expression : Expr} {values : List Value}
    (valid : literal.value=some expected)
    (actual : Args context before [.literal literal,expression] values after) :
    ∃value,values=[expected,value] ∧ Eval context before expression value after := by
  cases actual with
  | ordered permutation run positions =>
    simp only [List.length_cons,List.length_nil,List.range_succ,List.range_zero,
      List.nil_append] at permutation
    have orders := List.perm_pair.mp permutation
    rcases orders with rfl | rfl
    · cases run with
      | cons first rest =>
        obtain ⟨rfl,rfl⟩:=literal_exact valid first
        cases rest with
        | cons second tail =>
          cases tail
          refine ⟨_,?_,second⟩
          change List.Forall₂ _ [0,1] values at positions
          cases positions with
          | cons h0 rest =>
            cases rest with
            | cons h1 tail =>
              cases tail
              simp_all [List.lookup]
    · cases run with
      | cons second rest =>
        cases rest with
        | cons first tail =>
          obtain ⟨rfl,rfl⟩:=literal_exact valid first
          cases tail
          refine ⟨_,?_,second⟩
          change List.Forall₂ _ [0,1] values at positions
          cases positions with
          | cons h0 rest =>
            cases rest with
            | cons h1 tail =>
              cases tail
              simp_all [List.lookup]

def normExpression (p : InputLoader.Profile) : Expr :=
  .call (failureSourceFunction (isFap p)).name [.literal (.integer p.grid "ULL")]

def printfExpressions (p : InputLoader.Profile) : List Expr :=
  [.literal (.string "%llu\n"),.cast .ull (normExpression p)]

theorem norm_arguments (p : InputLoader.Profile) {F : Type} (context : Context F) (before : State F) :
    Args context before [.literal (.integer p.grid "ULL")] [.integer (integer64 p.grid)] before := by
  refine .ordered (evaluated:=[(0,.integer (integer64 p.grid))]) (List.Perm.refl _)
    (.cons (.literal _ _ (.integer (integer64 p.grid)) ?_) .nil) ?_
  · cases p <;> rfl
  · simp

theorem printf_arguments {F : Type} (context : Context F) (p : InputLoader.Profile)
    {before after : State F} {out : Nat} (fits : out<2^64)
    (actual : Call context (failureSourceFunction (isFap p)).name
      [.integer (integer64 p.grid)] before (.value (.integer (integer64 out))) after) :
    Args context before (printfExpressions p) [.string "%llu\n",.integer (integer64 out)] after := by
  refine .ordered (evaluated:=[(0,.string "%llu\n"),(1,.integer (integer64 out))])
    (List.Perm.refl _) (.cons (.literal _ _ _ rfl) (.cons ?_ .nil)) ?_
  · exact .cast (.call (norm_arguments p context before) actual) (SourceOutput.actual_printf_cast out fits)
  · exact .cons rfl (.cons rfl .nil)

/-- The unsigned argument sent to printf comes from the actual nested norm
Call and its real cast, for every argument order; it is never a fresh oracle. -/
theorem every_printf_arguments (p : InputLoader.Profile)
    (certificate : MainCertificate.Certificate p) {before after : State IOState} {values : List Value}
    (well : WellScoped before) (host : before.mode=.host)
    (actual : Args (ioContext p.program) before (printfExpressions p) values after) :
    ∃out,values=[.string "%llu\n",.integer (integer64 out)] ∧ out<2^64 ∧
      (out=AnswerSource.sentinel ∨ out=normAnswer p certificate) ∧
      Call (ioContext p.program) (failureSourceFunction (isFap p)).name
        [.integer (integer64 p.grid)] before (.value (.integer (integer64 out))) after := by
  obtain ⟨value,rfl,evaluated⟩:=two_arguments (by rfl : (Literal.string "%llu\n").value=some (.string "%llu\n")) actual
  cases evaluated with
  | load place read => cases place
  | cast evaluated converted =>
    cases evaluated with
    | load place read => cases place
    | call args called =>
      have unique:=ApplicationPureCall.args_unique (by simp [SourcePure.CallFree]) args (norm_arguments p (ioContext p.program) before)
      obtain ⟨rfl,_,rfl⟩:=unique
      have alternatives:=every_norm_call (ioContext p.program) p rfl certificate
        (io_hasMemory p.program) (io_sound p.program) well host called
      rcases alternatives with sentinel | success
      · cases sentinel
        have casted:=SourceOutput.actual_printf_cast AnswerSource.sentinel (by norm_num [AnswerSource.sentinel])
        have eq:=Option.some.inj (converted.symm.trans casted)
        subst value
        exact ⟨AnswerSource.sentinel,rfl,by norm_num [AnswerSource.sentinel],Or.inl rfl,called⟩
      · cases success
        have eq:=Option.some.inj (converted.symm.trans (SourceOutput.actual_printf_cast _ (normAnswer_fits p certificate)))
        subst value
        exact ⟨normAnswer p certificate,rfl,normAnswer_fits p certificate,Or.inr rfl,called⟩

end RH080Next.FFTPV.MainIO
