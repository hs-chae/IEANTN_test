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

def canonicalLog (n : Nat) : Nat := binaryLogUpper n (2^n.log2) n.log2
attribute [irreducible] canonicalLog

theorem canonical_bounds {n : Nat} (lower:2≤n) : 2^n.log2≤n ∧n<2*(2^n.log2) := by
  refine ⟨Nat.log2_self_le (by omega),?_⟩
  simpa only [pow_succ,Nat.mul_comm] using (Nat.lt_log2_self (n:=n))

theorem canonical_word {n : Nat} (lower:2≤n) (upper:n≤2000000000000) : canonicalLog n<2^64 := by
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

theorem log_value {n output : Nat} (source:FiniteLogUpperExecute.SourceExecution n output) :
    output=canonicalLog n := by
  obtain ⟨two,k,lower,upper,hp,low,high⟩:=source.normalized
  obtain ⟨t,actual⟩:=source.actual
  have bounds:=canonical_bounds lower
  have equal:=FiniteLogUpperExecute.completed_correct lower upper rfl bounds.1 bounds.2 actual
  have numbers:=congrArg WideScalar.Value.number equal
  change (output:Int)=(canonicalLog n:Int) at numbers
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
  change ((convertArguments [u64] [argument]).bind (fun args=>
    (service "rpc_log_upper" args).bind (WideScalar.cast u64)))=_
  rw [convertedArgs]
  change ((service "rpc_log_upper" [word64 n]).bind (WideScalar.cast u64))=_
  rw [served]
  exact casted

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


#print axioms reference_run
end RamanujanPV.FiniteCellGeneric
