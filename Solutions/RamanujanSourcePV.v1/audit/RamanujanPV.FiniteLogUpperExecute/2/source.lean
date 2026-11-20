/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteLogUpperPrefix
import RamanujanPV.FiniteLogNormalizationUnique
import RamanujanPV.FiniteLogSeriesExecute

/-! Generic whole-source correctness of rpc_log_upper. The combined service is
source-closed for every accepted ceil/series response, rather than an assumed
logarithm oracle or a bounded-interpreter completeness premise. -/
namespace RamanujanPV.FiniteLogUpperExecute
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open FiniteScalarMachine FiniteScalarWords FiniteScalarRules FiniteLogSeriesRules
open AnalyticTransition
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
abbrev P := FiniteLogSeriesExecute.P
abbrev C := FiniteLogSeriesExecute.service
abbrev input := FiniteLogUpperPrefix.input

def log2Expr : Expr := .call (.var "rpc_log_series_upper") [.nat 1,.nat 3]
def mantissaExpr : Expr := .call (.var "rpc_log_series_upper") [
  .binary "-" (.var "n") (.var "two"),.binary "+" (.var "n") (.var "two")]
def resultExpr : Expr := .call (.var "rpc_log_ceildiv") [
  .binary "+" (.binary "*" (.cast "__uint128_t" (.var "k")) (.var "log2")) mantissaExpr,
  .nat 1048576]
def suffixStatements : List Stmt := [
  .declare [⟨"uint64_t","log2",some log2Expr⟩],.returnStmt resultExpr]
def withLog2 (s : State) : State :=
  ⟨FiniteScalarMachine.bind s.env "log2" (word64 (fixedLogSeries 1 3))⟩

theorem actual_source_body : FiniteLogSource.upperFunction.body=
    .sequence (FiniteLogUpperPrefix.prefixStatements++suffixStatements) := rfl

lemma log2_pure {s : State} : pure P C s.env 8 log2Expr=
    some (word64 (fixedLogSeries 1 3)) :=
  pure_call2 (pure_literal (by decide +kernel : literal 1=some (i32 1)))
    (pure_literal (by decide +kernel : literal 3=some (i32 3)))
    (FiniteLogSeriesExecute.invoke_series (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))

lemma log2_declare {s : State} (fresh : s.env "log2"=none) :
    Declare P C [⟨"uint64_t","log2",some log2Expr⟩] s (withLog2 s) :=
  declare_one_of rfl fresh log2_pure
    (cast64 (FiniteLogBounds.fixed_series_u64 (by norm_num) (by norm_num)))

lemma normalized_after_declare {s : State} {n two k : Nat}
    (h : FiniteLogNormalize.Normalized s n two k) :
    FiniteLogNormalize.Normalized (withLog2 s) n two k := by
  refine ⟨?_,?_,?_,h.power,h.low,h.high,h.bound⟩
  · simpa [withLog2,FiniteScalarMachine.bind,Function.update] using h.read_n
  · simpa [withLog2,FiniteScalarMachine.bind,Function.update] using h.read_two
  · simpa [withLog2,FiniteScalarMachine.bind,Function.update] using h.read_k

lemma add64 {a b : Nat} (ha : a<2^64) (hb : b<2^64) (hab : a+b<2^64) :
    WideScalar.binary "+" (word64 a) (word64 b)=some (word64 (a+b)) := by
  simpa only [word64,scalarWord,unsignedType,u64,←Nat.cast_add] using
    FiniteScalarRules.add (by decide : 0<64) (FiniteCellWords.operands64 ha hb)
      (show Range 64 ((word64 a).number+(word64 b).number) by
        simpa only [word64,←Nat.cast_add] using range_nat hab)

lemma mantissa_pure {s : State} {n two k : Nat} {fuel : Nat}
    (h : FiniteLogNormalize.Normalized s n two k) (upper : n≤2000000000000) :
    pure P C s.env (fuel+3) mantissaExpr=
      some (word64 (fixedLogSeries (n-two) (n+two))) := by
  have domain := FiniteLogNormalize.subsequent_argument_bounds h upper
  have nb : n<2^64 := by norm_num at upper ⊢;omega
  have tb : two<2^64 := h.low.trans_lt nb
  have subWord : n-two<2^64 := (Nat.sub_le n two).trans_lt nb
  have sub : pure P C s.env (fuel+2) (.binary "-" (.var "n") (.var "two"))=
      some (word64 (n-two)) :=
    FiniteScalarMachine.pure_binary (pure_variable h.read_n) (pure_variable h.read_two)
      (sub64 nb tb h.low)
  have add : pure P C s.env (fuel+2) (.binary "+" (.var "n") (.var "two"))=
      some (word64 (n+two)) :=
    FiniteScalarMachine.pure_binary (pure_variable h.read_n) (pure_variable h.read_two)
      (add64 nb tb domain.2.2.1)
  exact pure_call2 sub add (FiniteLogSeriesExecute.invoke_series (cast64 subWord)
    (cast64 domain.2.2.1) subWord domain.2.2.1 domain.1 domain.2.1)

lemma result_pure {s : State} {n two k : Nat}
    (h : FiniteLogNormalize.Normalized s n two k) (upper : n≤2000000000000)
    (readLog2 : s.env "log2"=some (word64 (fixedLogSeries 1 3))) :
    pure P C s.env 8 resultExpr=some (word64 (binaryLogUpper n two k)) := by
  have domain := FiniteLogNormalize.subsequent_argument_bounds h upper
  have logWord : fixedLogSeries 1 3<2^64 :=
    FiniteLogBounds.fixed_series_u64 (by norm_num) (by norm_num)
  have mantissaWord : fixedLogSeries (n-two) (n+two)<2^64 :=
    FiniteLogBounds.fixed_series_u64 domain.1 domain.2.1
  have product : k*fixedLogSeries 1 3<2^128 :=
    FinitePredicateBounds.word_product domain.2.2.2 logWord
  have numerator := FiniteLogBounds.binary_numerator_u128 h.low h.high h.bound
  have outWord := FiniteLogBounds.binary_output_u64 h.low h.high h.bound
  have kCast : pure P C s.env 5 (.cast "__uint128_t" (.var "k"))=some (word128 k) :=
    pure_cast rfl (pure_variable h.read_k) (word64_cast128 domain.2.2.2)
  have mul : pure P C s.env 6
      (.binary "*" (.cast "__uint128_t" (.var "k")) (.var "log2"))=
      some (word128 (k*fixedLogSeries 1 3)) :=
    FiniteScalarMachine.pure_binary kCast (pure_variable readLog2)
      (FiniteCellWords.u128_mul64 (domain.2.2.2.trans (by norm_num)) logWord product)
  have add : pure P C s.env 7
      (.binary "+" (.binary "*" (.cast "__uint128_t" (.var "k")) (.var "log2")) mantissaExpr)=
      some (word128 (k*fixedLogSeries 1 3+fixedLogSeries (n-two) (n+two))) :=
    FiniteScalarMachine.pure_binary mul (mantissa_pure (fuel:=3) h upper)
      (add128_64 product mantissaWord numerator)
  exact pure_call2 add (pure_literal (by decide +kernel : literal 1048576=some (i32 1048576)))
    (FiniteLogSeriesExecute.invoke_ceil (cast128 numerator) (by decide +kernel)
      numerator (by norm_num) (by norm_num) outWord)

lemma close_input {s : State} {n : Nat} (read : s.env "n"=some (word64 n)) :
    closeScope (input n) s=input n := by
  apply congrArg State.mk
  funext name
  by_cases hn : name="n"
  · subst name
    simp [closeScope,input,FiniteLogUpperPrefix.input,read]
  · simp [closeScope,input,FiniteLogUpperPrefix.input,hn]

lemma seq_append {xs ys : List Stmt} {s t : State} {out : Flow}
    (first : SeqRun P C xs s (.continuing t)) (rest : SeqRun P C ys t out) :
    SeqRun P C (xs++ys) s out := by
  induction xs generalizing s with
  | nil => cases first;exact rest
  | cons head tail ih =>
    cases first with
    | next headRun tailRun => exact SeqRun.next headRun (ih tailRun rest)

/-- Entire actual rpc_log_upper body, including argument-derived initialization,
all calls, actual return conversion and lexical cleanup. The given two/k merely
identify the unique binary cell, not an assumed program output. -/
theorem function_executes {n two k : Nat} (lower : 2≤n) (upper : n≤2000000000000)
    (hp : two=2^k) (low : two≤n) (high : n<2*two) :
    Run P C FiniteLogSource.upperFunction.body (input n)
      (.returned (input n) (word64 (binaryLogUpper n two k))) := by
  obtain ⟨s,two',k',pref,post,fresh,frame⟩ :=
    FiniteLogUpperPrefix.prefix_exec (p:=P) (c:=C) lower upper
  obtain ⟨twos,ks⟩ := FiniteLogNormalizationUnique.unique hp low high post.power post.low post.high
  subst two'
  subst k'
  have after := normalized_after_declare post
  have returned : Eval P C resultExpr (withLog2 s) (withLog2 s)
      (word64 (binaryLogUpper n two k)) := by
    have value := result_pure after upper
      (by simp [withLog2,FiniteScalarMachine.bind,Function.update])
    change (do return (withLog2 s,←pure P C (withLog2 s).env 8 resultExpr))=some _
    rw [value]
    rfl
  rw [actual_source_body]
  apply StmtRun.sequence (seq_append pref
    (SeqRun.next (StmtRun.declare (log2_declare fresh)) (SeqRun.returned (StmtRun.returnValue returned))))
  change Flow.returned (input n) (word64 (binaryLogUpper n two k))=
    Flow.returned (closeScope (input n) (withLog2 s)) (word64 (binaryLogUpper n two k))
  rw [close_input after.read_n]

/-- All completed source runs agree with the source-proved mathematical result. -/
theorem completed_correct {n two k : Nat} {t : State} {answer : Value}
    (lower : 2≤n) (upper : n≤2000000000000)
    (hp : two=2^k) (low : two≤n) (high : n<2*two)
    (actual : Run P C FiniteLogSource.upperFunction.body (input n) (.returned t answer)) :
    answer=word64 (binaryLogUpper n two k) := by
  have eq := FiniteScalarMachine.run_unique (function_executes lower upper hp low high) actual
  have values := congrArg (fun flow : Flow=>match flow with
    | .returned _ value=>some value | .continuing _=>none) eq
  exact (Option.some.inj values).symm

#print axioms actual_source_body
#print axioms result_pure
#print axioms function_executes
#print axioms completed_correct
end RamanujanPV.FiniteLogUpperExecute
