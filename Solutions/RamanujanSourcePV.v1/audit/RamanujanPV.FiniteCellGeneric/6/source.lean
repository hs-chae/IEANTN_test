import RamanujanPV.FiniteCellProtected
import RamanujanPV.FiniteLogUpperExecute
namespace RamanujanPV.FiniteCellGeneric
open FiniteScalarMachine FiniteScalarWords FiniteScalarRules FiniteLogSeriesRules
open FiniteCellProtected AnalyticTransition WindowCells LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
abbrev P := FiniteCellExecution.prototypes

theorem invoke_of {p : Prototypes} {c : Service} {name : String}
    {prototype : Prototype} {args converted : List Value} {value output : Value}
    (hp:p name=some prototype) (ha:convertArguments prototype.arguments args=some converted)
    (hc:c name converted=some value) (ho:WideScalar.cast prototype.result value=some output) :
    invoke p c name args=some output := by
  simp only [invoke,hp,Bind.bind,Option.bind,ha,hc,ho]

def canonicalLog (n : Nat) : Nat := binaryLogUpper n (2^n.log2) n.log2
attribute [irreducible] canonicalLog

theorem canonical_bounds {n : Nat} (lower:2≤n) : 2^n.log2≤n ∧n<2*(2^n.log2) := by
  refine ⟨Nat.log2_self_le (by omega),?_⟩
  simpa only [pow_succ,Nat.mul_comm] using (Nat.lt_log2_self (n:=n))

theorem canonical_word {n : Nat} (lower:2≤n) (upper:n≤2000000000000) : canonicalLog n<2^64 := by
  unfold canonicalLog
  have bounds:=canonical_bounds lower
  exact FiniteLogBounds.binary_output_u64 bounds.1 bounds.2
    (FiniteLogBounds.normalization_k_bound rfl bounds.1 upper)

/-- Fast callee contracts are backed by universal actual-source execution.
Neither a log oracle nor the old128-fuel interpreter is used. -/
def service : Service := fun name args=>
  if name="rpc_e_low" then match args with
    | []=>some (word64 3133965575612453533) | _=>none
  else if name="rpc_e_high" then match args with
    | []=>some (word64 3133965575612453555) | _=>none
  else if name="rpc_log_upper" then match args with
    | [n]=>if n.type=u64 ∧0≤n.number ∧n.number<2^64 ∧2≤n.number.toNat ∧
        n.number.toNat≤2000000000000
      then some (word64 (canonicalLog n.number.toNat)) else none
    | _=>none
  else none

attribute [irreducible] service

theorem log_value {n output : Nat} (source:FiniteLogUpperExecute.SourceExecution n output) :
    output=canonicalLog n := by
  obtain ⟨two,k,lower,upper,hp,low,high⟩:=source.normalized
  obtain ⟨t,actual⟩:=source.actual
  have bounds:=canonical_bounds lower
  have equal:=FiniteLogUpperExecute.completed_correct lower upper rfl bounds.1 bounds.2 actual
  have numbers:=congrArg WideScalar.Value.number equal
  change (output:Int)=(binaryLogUpper n (2^n.log2) n.log2:Int) at numbers
  unfold canonicalLog
  exact Int.ofNat.inj numbers

theorem invoke_log {n : Nat} {argument : Value}
    (converted:WideScalar.cast u64 argument=some (word64 n))
    (lower:2≤n) (upper:n≤2000000000000) :
    invoke P service "rpc_log_upper" [argument]=some (word64 (canonicalLog n)) := by
  have convertedArgs : convertArguments [u64] [argument]=some [word64 n] := by
    simp only [convertArguments]
    rw [converted]
    rfl
  have word:n<2^64:=upper.trans_lt (by norm_num)
  have nn:(0:Int)≤n:=by omega
  have nw:(n:Int)<2^64:=by exact_mod_cast word
  have served:service "rpc_log_upper" [word64 n]=some (word64 (canonicalLog n)) := by
    simp only [service,word64,↓reduceIte,Int.toNat_natCast,nn,nw,lower,upper,and_self]
    rfl
  have casted:=FiniteLogSeriesRules.cast64 (n:=canonicalLog n) (canonical_word lower upper)
  exact invoke_of (p:=P) (c:=service) (name:="rpc_log_upper")
    (prototype:=⟨u64,[u64]⟩) (by rfl) convertedArgs served casted

/-- Numerical applicability has no desired strict inequality. The logarithm
field is itself an actual source execution, constructed generically from the
unchanged mathematical metadata by FiniteLogUpperExecute. -/
structure Domain (r : RawFactoredCell) extends WordFits r : Prop where
  nLower : 38358837683≤r.n
  advance : r.n<r.next
  upper : r.next≤2000000000001
  jBound : r.j≤r.n
  qBound : r.Q≤r.j
  pBound : r.P≤r.next-1
  logPositive : 0<r.Lu
  logSource : FiniteLogUpperExecute.SourceExecution r.n r.Lu
  jExp : r.j*eHi≤r.n*2^60
  aFloor : r.A=(r.n*eLo)/r.Lu

theorem Domain.logResponse {r : RawFactoredCell} (domain:Domain r) :
    invoke P service "rpc_log_upper" [word64 r.n]=some (word64 r.Lu) := by
  have lower:2≤r.n:=by have h:=domain.nLower;omega
  have upper:r.n≤2000000000000:=by have h:=domain.advance;have h':=domain.upper;omega
  rw [log_value domain.logSource]
  exact invoke_log (FiniteLogSeriesRules.cast64 domain.nWord) lower upper

theorem log_eval {r : RawFactoredCell} {s : State}
    (fields:Inputs r s.env) (fits:WordFits r)
    (response:invoke P service "rpc_log_upper" [word64 r.n]=some (word64 r.Lu)) :
    Eval P service (.binary "!=" (.var "Lu") (.call (.var "rpc_log_upper") [.var "n"]))
      s s (WideScalar.boolean false) := by
  apply eval_compare_of (by simp) (FiniteScalarRules.pure_variable fields.luValue)
    (call_one fields.nValue response)
  simpa using FiniteCellWords.u64_ne fits.luWord fits.luWord

theorem low_response : invoke P service "rpc_e_low" []=some (word64 eLo) := by
  unfold invoke P FiniteCellExecution.prototypes service
  decide

theorem high_response : invoke P service "rpc_e_high" []=some (word64 eHi) := by
  unfold invoke P FiniteCellExecution.prototypes service
  decide

theorem low_declare (r : RawFactoredCell) :
    Declare P service [⟨"uint64_t","lo",some (.call (.var "rpc_e_low") [])⟩]
      (FiniteCellExecution.input r) (withLow r) :=
  declare_u64 rfl (call_none low_response) (by norm_num [eLo])

theorem high_declare (r : RawFactoredCell) :
    Declare P service [⟨"uint64_t","hi",some (.call (.var "rpc_e_high") [])⟩]
      (withLow r) (withBoth r) :=
  declare_u64 rfl (call_none high_response) (by norm_num [eHi,eLo])

theorem reference_run {r : RawFactoredCell} (domain : Domain r) :
    Run P service
      FiniteCellSource.cellFunction.body (FiniteCellExecution.input r)
      (.returned (FiniteCellExecution.input r)
        (WideScalar.boolean (decide ((2^20*r.P)*r.P<r.A*r.Q)))) := by
  let p:=P
  let c:=service
  have fields:=input_fields r
  have fits:=domain.toWordFits
  have fBoth:=both_fields r
  have hp : r.P≤2000000000000 := by
    have h:=domain.pBound
    have h':=domain.upper
    omega
  have first0 : Run p c nGuard (FiniteCellExecution.input r) (.continuing (FiniteCellExecution.input r)) :=
    reject_false (n_eval fields fits) (by simp only [decide_eq_false_iff_not];exact Nat.not_lt.mpr domain.nLower)
  have first1 : Run p c advanceGuard (FiniteCellExecution.input r) (.continuing (FiniteCellExecution.input r)) :=
    reject_false (advance_eval fields fits) (by simp only [decide_eq_false_iff_not];exact Nat.not_le.mpr domain.advance)
  have first2 : Run p c upperGuard (FiniteCellExecution.input r) (.continuing (FiniteCellExecution.input r)) :=
    reject_false (upper_eval fields fits) (by simp only [decide_eq_false_iff_not];exact Nat.not_lt.mpr domain.upper)
  have first3 : Run p c jGuard (FiniteCellExecution.input r) (.continuing (FiniteCellExecution.input r)) :=
    reject_false (j_eval fields fits) (by simp only [decide_eq_false_iff_not];exact Nat.not_lt.mpr domain.jBound)
  have first4 : Run p c qGuard (FiniteCellExecution.input r) (.continuing (FiniteCellExecution.input r)) :=
    reject_false (q_eval fields fits) (by simp only [decide_eq_false_iff_not];exact Nat.not_lt.mpr domain.qBound)
  have first5 : Run p c pGuard (FiniteCellExecution.input r) (.continuing (FiniteCellExecution.input r)) :=
    reject_false (p_eval fields fits (by have h:=domain.advance;omega))
      (by simp only [decide_eq_false_iff_not];exact Nat.not_lt.mpr domain.pBound)
  have first6 : Run p c logPositiveGuard (FiniteCellExecution.input r) (.continuing (FiniteCellExecution.input r)) :=
    reject_false (log_positive_eval fields fits) (by simp only [decide_eq_false_iff_not];exact ne_of_gt domain.logPositive)
  have first7 : Run p c logGuard (FiniteCellExecution.input r) (.continuing (FiniteCellExecution.input r)) :=
    reject_false (log_eval fields fits domain.logResponse) rfl
  have first10 : Run p c jProductGuard (withBoth r) (.continuing (withBoth r)) :=
    reject_false (j_exp_eval fBoth fits (by rfl))
      (by simp only [decide_eq_false_iff_not];exact Nat.not_lt.mpr domain.jExp)
  have first11 : Run p c aGuard (withBoth r) (.continuing (withBoth r)) :=
    reject_false (a_eval fBoth fits (by rfl) domain.logPositive)
      (by simp only [decide_eq_false_iff_not];exact not_ne_iff.mpr domain.aFloor)
  rw [actual_body]
  apply StmtRun.sequence
    (SeqRun.next first0 (SeqRun.next first1 (SeqRun.next first2
      (SeqRun.next first3 (SeqRun.next first4 (SeqRun.next first5
      (SeqRun.next first6 (SeqRun.next first7
      (SeqRun.next (StmtRun.declare (low_declare r))
      (SeqRun.next (StmtRun.declare (high_declare r))
      (SeqRun.next first10 (SeqRun.next first11
      (SeqRun.returned (StmtRun.returnValue (strict_eval fBoth fits hp)))))))))))))))
  change Flow.returned (FiniteCellExecution.input r) _=Flow.returned (closeScope _ (withBoth r)) _
  rw [final_scope]


def CalleeExecution (name : String) (args : List Value) (answer : Value) : Prop :=
  (name="rpc_e_low" ∧args=[] ∧∃t,
    Run FiniteWideExpExecute.noPrototypes FiniteWideExpExecute.noCalls
      FiniteExpSource.lowFunction.body empty (.returned t answer)) ∨
  (name="rpc_e_high" ∧args=[] ∧∃t,FiniteWideExpLinked.LinkedHighRun t answer) ∨
  (name="rpc_log_upper" ∧∃n,args=[word64 n] ∧answer=word64 (canonicalLog n) ∧
    FiniteLogUpperExecute.SourceExecution n (canonicalLog n))

/-- Every fast scalar helper response is backed by actual unchanged C source.
The old bounded source registries and all old numerical receipts are untouched. -/
theorem service_closed {name : String} {args : List Value} {answer : Value}
    (response:service name args=some answer) : CalleeExecution name args answer := by
  unfold service at response
  by_cases low:name="rpc_e_low"
  · subst name
    cases args with
    | nil=>
      have equal:word64 3133965575612453533=answer := by
        simpa only [↓reduceIte,Option.some.injEq] using response
      subst answer
      exact Or.inl ⟨rfl,rfl,FiniteWideExpExecute.low_source_run⟩
    | cons a rest=>simp at response
  · by_cases high:name="rpc_e_high"
    · subst name
      cases args with
      | nil=>
        have equal:word64 3133965575612453555=answer := by
          simpa only [low,↓reduceIte,Option.some.injEq] using response
        subst answer
        exact Or.inr (Or.inl ⟨rfl,rfl,FiniteWideExpLinked.linked_high_source⟩)
      | cons a rest=>simp [low] at response
    · by_cases logarithm:name="rpc_log_upper"
      · subst name
        simp only [low,high,↓reduceIte] at response
        cases args with
        | nil=>simp at response
        | cons n rest=>
          cases rest with
          | cons a rest=>simp at response
          | nil=>
            simp only at response
            split at response
            next h=>
              rcases h with ⟨ntype,nn,nword,nlower,nupper⟩
              have nv:n=word64 n.number.toNat := by
                cases n with
                | mk type number=>
                  simp only at ntype nn ⊢
                  cases ntype
                  simp only [word64,Int.toNat_of_nonneg nn]
              have equal:answer=word64 (canonicalLog n.number.toNat):=(Option.some.inj response).symm
              refine Or.inr (Or.inr ⟨rfl,n.number.toNat,?_,equal,?_⟩)
              · exact congrArg (fun v=>[v]) nv
              · have bounds:=canonical_bounds nlower
                apply FiniteLogUpperExecute.source_execution_from_math
                  (n:=n.number.toNat) (two:=2^n.number.toNat.log2) (k:=n.number.toNat.log2)
                  (output:=canonicalLog n.number.toNat) nlower nupper rfl bounds.1 bounds.2
                unfold canonicalLog
                rfl
            next h=>contradiction
      · simp only [low,high,logarithm,↓reduceIte] at response
        contradiction

structure SourceExecution (r : RawFactoredCell) : Prop where
  actual : ∃t,Run P service FiniteCellSource.cellFunction.body (FiniteCellExecution.input r)
    (.returned t (i32 1))
  source : LCMSourcePV.RestrictedC.SourceCorresponds FiniteCellSource.render
    FiniteCellSource.actualSource ()
  eSource : LCMSourcePV.RestrictedC.SourceCorresponds FiniteExpSource.render
    FiniteExpSource.actualSource ()
  logSource : LCMSourcePV.RestrictedC.SourceCorresponds FiniteLogSource.render
    FiniteLogSource.actualSource ()
  helpers : ∀name args answer,service name args=some answer→CalleeExecution name args answer
  logHelpers : ∀name args answer,FiniteLogSeriesExecute.service name args=some answer→
    FiniteLogSeriesExecute.CalleeExecution name args answer
  leafHelpers : ∀name args answer,FiniteLogServices.ceilService name args=some answer→
    name="rpc_log_ceildiv" ∧∃t,Run FiniteLogCeil.prototypes FiniteLogCeil.noCalls
      FiniteLogSource.ceilFunction.body (FiniteLogServices.sourceInput args) (.returned t answer)

/-- A proved exact mathematical result is transported through generic ACTUAL
C execution. This is refinement of the full source algorithm, not an output
oracle or an assumption that a native computation returned the desired result. -/
theorem source_execution_from_math {r : RawFactoredCell} (domain:Domain r)
    (strict:2^20*r.P^2<r.A*r.Q) : SourceExecution r := by
  have comparison : decide ((2^20*r.P)*r.P<r.A*r.Q)=true := by
    apply decide_eq_true
    simpa only [pow_two,Nat.mul_assoc] using strict
  have actual:=reference_run domain
  refine ⟨⟨FiniteCellExecution.input r,?_⟩,FiniteCellSource.actual_source_checked,
    FiniteExpSource.actual_source_checked,FiniteLogSource.actual_source_checked,
    (fun _ _ _ h=>service_closed h),(fun _ _ _ h=>FiniteLogSeriesExecute.service_closed h),
    (fun _ _ _ h=>FiniteLogServices.ceil_service_closed h)⟩
  simpa only [comparison,WideScalar.boolean,i32] using actual

/-- Every completed positive source run on the stated non-strict source domain
forces the mathematical strict comparison by actual source determinism. -/
theorem positive_implies_strict {r : RawFactoredCell} (domain:Domain r)
    (actual:SourceExecution r) : 2^20*r.P^2<r.A*r.Q := by
  obtain ⟨finish,run⟩:=actual.actual
  have equal:=FiniteScalarMachine.run_unique (reference_run domain) run
  have outputs : WideScalar.boolean (decide ((2^20*r.P)*r.P<r.A*r.Q))=i32 1 :=
    (LCMSourcePV.ASTLoops.Flow.returned.inj equal).2
  have strict:=of_decide_eq_true ((FiniteCellWords.boolean_eq_one _).mp outputs)
  exact FinitePredicateBounds.strict_scaled_square strict

#print axioms reference_run
#print axioms service_closed
#print axioms source_execution_from_math
#print axioms positive_implies_strict
end RamanujanPV.FiniteCellGeneric
