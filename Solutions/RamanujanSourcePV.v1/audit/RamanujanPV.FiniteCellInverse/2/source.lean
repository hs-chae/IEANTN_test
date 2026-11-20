/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteCellSound
import RamanujanPV.FiniteCellProtected

/-! Actual positive source execution discharges its own input-domain guards.
Only C-argument representability is an applicability assumption. No strict
inequality, successful-effect or prevalidated guard is assumed. -/
namespace RamanujanPV.FiniteCellInverse
open FiniteScalarMachine FiniteCellTrace FiniteCellProtected FiniteCellSound
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

structure Prefix (r : RawFactoredCell) extends WordFits r : Prop where
  nLower : 38358837683 ≤ r.n
  advance : r.n < r.next
  upper : r.next ≤ 2000000000001
  jBound : r.j ≤ r.n
  qBound : r.Q ≤ r.j
  pBound : r.P ≤ r.next-1
  logPositive : 0 < r.Lu

/-- The first seven actual tests cannot be bypassed by a positive return;
all their evaluations preserve the input environment. -/
theorem trace_prefix {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fits : WordFits r) (fields : Inputs r s.env) (tr : Trace p c s) :
    tr.s7=s ∧ Prefix r := by
  have h0 := false_test (n_eval fields fits) tr.guard0
  have g1 := tr.guard1
  rw [h0.1] at g1
  have h1 := false_test (advance_eval fields fits) g1
  have g2 := tr.guard2
  rw [h1.1] at g2
  have h2 := false_test (upper_eval fields fits) g2
  have g3 := tr.guard3
  rw [h2.1] at g3
  have h3 := false_test (j_eval fields fits) g3
  have g4 := tr.guard4
  rw [h3.1] at g4
  have h4 := false_test (q_eval fields fits) g4
  have positive : 0<r.next := by omega
  have g5 := tr.guard5
  rw [h4.1] at g5
  have h5 := false_test (p_eval fields fits positive) g5
  have g6 := tr.guard6
  rw [h5.1] at g6
  have h6 := false_test (log_positive_eval fields fits) g6
  exact ⟨h6.1,⟨fits,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩⟩

theorem positive_prefix {r : RawFactoredCell} {s : State}
    (fits : WordFits r)
    (actual : Run FiniteCellExecution.prototypes FiniteCellExecution.service
      FiniteCellSource.cellFunction.body (FiniteCellExecution.input r) (.returned s (i32 1))) :
    Prefix r := by
  obtain ⟨tr⟩ := positive_trace actual
  exact (trace_prefix fits (input_fields r) tr).2

lemma cast64_result {value out : Value}
    (casted : WideScalar.cast u64 value=some out) :
    ∃n : Nat,n<2^64 ∧out=word64 n := by
  change some (⟨u64,value.number%(2: Int)^64⟩:Value)=some out at casted
  have nonnegative := Int.emod_nonneg value.number (by norm_num : (2:Int)^64≠0)
  have below := Int.emod_lt_of_pos value.number (by norm_num : (0:Int)<2^64)
  let n := (value.number%(2:Int)^64).toNat
  have exactNumber : (n:Int)=value.number%(2:Int)^64 := Int.toNat_of_nonneg nonnegative
  refine ⟨n,?_,?_⟩
  · have bound : (n:Int)<(2:Int)^64 := by rw [exactNumber];exact below
    exact_mod_cast bound
  · have equal := (Option.some.inj casted).symm
    rw [equal]
    apply congrArg (fun z:Int=>(⟨u64,z⟩:Value))
    exact exactNumber.symm

lemma invoke64_result {p : Prototypes} {c : Service} {name : String}
    {types : List CIntType} {args : List Value} {out : Value}
    (prototype : p name=some ⟨u64,types⟩)
    (response : invoke p c name args=some out) :
    ∃n : Nat,n<2^64 ∧out=word64 n := by
  unfold invoke at response
  rw [prototype] at response
  simp only [Option.bind] at response
  cases converted : convertArguments types args with
  | none=>simp [converted] at response
  | some arguments=>
    simp only [converted,Option.bind] at response
    cases returned : c name arguments with
    | none=>simp [returned] at response
    | some value=>
      simp only [returned,Option.bind] at response
      exact cast64_result response

theorem log_response_of_guard {r : RawFactoredCell} {s t : State}
    (fits : WordFits r) (fields : Inputs r s.env)
    (guard : FalseCondition FiniteCellExecution.prototypes FiniteCellExecution.service g7 s t) :
    t=s ∧invoke FiniteCellExecution.prototypes FiniteCellExecution.service
      "rpc_log_upper" [word64 r.n]=some (word64 r.Lu) := by
  cases response : invoke FiniteCellExecution.prototypes FiniteCellExecution.service
      "rpc_log_upper" [word64 r.n] with
  | none=>
    obtain ⟨v,evaluated,stop⟩ := guard
    simp only [Eval,eval,g7,FiniteScalarMachine.pure,List.mapM,List.mapM.loop,
      List.reverse,List.reverseAux,fields.luValue,fields.nValue,Option.bind,Bind.bind,Pure.pure,response] at evaluated
    contradiction
  | some answer=>
    obtain ⟨n,bound,equal⟩ := invoke64_result (show FiniteCellExecution.prototypes "rpc_log_upper"=some ⟨u64,[u64]⟩ by rfl) response
    rw [equal] at response
    have known := eval_compare_of (by simp : ("!=" : String)="<" ∨"!="="<=" ∨"!="=">" ∨"!="="==" ∨"!="="!=")
      (FiniteScalarRules.pure_variable fields.luValue)
      (call_one fields.nValue response) (FiniteCellWords.u64_ne fits.luWord bound)
    have result := false_test known guard
    have same : r.Lu=n := by omega
    rw [←same] at response
    exact ⟨result.1,response⟩

/-- Every non-strict guard is recovered from the actual source execution.
The separate application premise is only seven valid uint64 arguments. -/
theorem positive_domain {r : RawFactoredCell} {t : State} (fits : WordFits r)
    (actual : Run FiniteCellExecution.prototypes FiniteCellExecution.service
      FiniteCellSource.cellFunction.body (FiniteCellExecution.input r) (.returned t (i32 1))) :
    Domain r ∧NumericPost r := by
  obtain ⟨tr⟩ := positive_trace actual
  have fields := input_fields r
  obtain ⟨s7,pre⟩ := trace_prefix fits fields tr
  have g7 := tr.guard7
  rw [s7] at g7
  obtain ⟨s8,logResponse⟩ := log_response_of_guard fits fields g7
  have low := tr.low
  rw [s8] at low
  have s9 : tr.s9=withLow r := Option.some.inj (low.symm.trans (low_declare r))
  have high := tr.high
  rw [s9] at high
  have s10 : tr.s10=withBoth r := Option.some.inj (high.symm.trans (high_declare r))
  have g8 := tr.guard8
  rw [s10] at g8
  obtain ⟨s11,indexFalse⟩ := false_test (j_exp_eval (both_fields r) fits (by rfl)) g8
  have index : r.j*WindowCells.eHi ≤ r.n*2^60 := by omega
  have g9 := tr.guard9
  rw [s11] at g9
  obtain ⟨s12,floorFalse⟩ := false_test (a_eval (both_fields r) fits (by rfl) pre.logPositive) g9
  have factor : r.A=(r.n*WindowCells.eLo)/r.Lu := by omega
  have returning := tr.returned
  rw [s12] at returning
  have pBound : r.P≤2000000000000 := by have := pre.pBound;have := pre.upper;omega
  obtain ⟨finish,strict⟩ := true_return (strict_eval (both_fields r) fits pBound) returning
  refine ⟨⟨fits,pre.nLower,pre.advance,pre.upper,pre.jBound,pre.qBound,pre.pBound,
    pre.logPositive,logResponse,index,factor⟩,
    ⟨pre.advance,pre.logPositive,index,factor,by simpa only [pow_two,Nat.mul_assoc] using strict⟩⟩


theorem positive_fixed {r : RawFactoredCell} (fits : WordFits r)
    (execution : FiniteCellExecution.SourceExecution r) :
    (r.toCell WindowCells.eLo WindowCells.eHi).FixedPredicate := by
  obtain ⟨state,actual⟩ := execution.actual
  exact numeric_post_fixed (positive_domain fits actual).2

#print axioms cast64_result
#print axioms invoke64_result
#print axioms log_response_of_guard
#print axioms positive_domain
#print axioms positive_fixed
#print axioms trace_prefix
#print axioms positive_prefix
end RamanujanPV.FiniteCellInverse
