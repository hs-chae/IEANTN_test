/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.PrimeWindow
import RamanujanPV.AnalyticGlue
import RamanujanPV.AnalyticTransition

/-! Real-cell consumption of checked local prime-count increments. The two
original base source executions remain explicit until their actual numeric
proofs close. All new classifications, arithmetic, logarithms and coverage must
be supplied by completed kernel certificate checks, never by a desired-gap premise. -/
namespace RamanujanPV.WindowCells
open QuotientDemandCheck PrimeWindow QuotientCCell AnalyticTransition
set_option autoImplicit false
set_option maxHeartbeats 2000000

def eLo : Nat := 3133965575612453533
def eHi : Nat := eLo+22

noncomputable def offsetValue (entries : Lean.RArray PrimeWindow.Entry) (offset : Nat) : Nat :=
  if offset=0 then 0 else (entries.get (offset-1)).cumulative

lemma count_offset {base count offset : Nat} {primes : Lean.RArray Nat} {primeCount : Nat}
    {entries : Lean.RArray PrimeWindow.Entry}
    (good : ∀ j, j < primeCount → Nat.Prime (primes.get j))
    (checked : PrimeWindow.checkAll base primes primeCount entries count=true)
    (bound : offset ≤ count) :
    Nat.primeCounting (base+offset)=Nat.primeCounting base+offsetValue entries offset := by
  by_cases zero : offset=0
  · simp [zero,offsetValue]
  · have h := PrimeWindow.count_at good checked (i:=offset-1) (by omega)
    have eq : base+(offset-1)+1=base+offset := by omega
    rw [eq] at h
    simpa [offsetValue,zero] using h

/-- All fields are ordinary integer arithmetic and exact lookup identities. -/
def RowSpec (pBase qBase pCount qCount pValue qValue : Nat)
    (pEntries qEntries : Lean.RArray PrimeWindow.Entry) (r : RawFactoredCell) : Prop :=
  pBase ≤ r.n ∧ r.n < r.next ∧ r.next ≤ pBase+pCount+1 ∧
  qBase ≤ r.j ∧ r.j ≤ qBase+qCount ∧
  r.P=pValue+offsetValue pEntries (r.next-1-pBase) ∧
  r.Q=qValue+offsetValue qEntries (r.j-qBase) ∧
  0 < r.Lu ∧ r.j*eHi ≤ r.n*2^60 ∧ r.A*r.Lu ≤ r.n*eLo ∧
  2^20*r.P^2 < r.A*r.Q ∧ 2^35 ≤ r.n ∧ r.n < 2^36 ∧
  r.Lu=binaryLogUpper r.n (2^35) 35 ∧
  2 ≤ r.next-1 ∧ r.next-1 ≤ 2000000000000 ∧ 2 ≤ r.j ∧ r.j ≤ 2000000000000

noncomputable instance rowSpecDecidable (pBase qBase pCount qCount pValue qValue : Nat)
    (pEntries qEntries : Lean.RArray PrimeWindow.Entry) (r : RawFactoredCell) :
    Decidable (RowSpec pBase qBase pCount qCount pValue qValue pEntries qEntries r) := by
  unfold RowSpec
  infer_instance

noncomputable def checkRow (pBase qBase pCount qCount pValue qValue stop count : Nat)
    (pEntries qEntries : Lean.RArray PrimeWindow.Entry) (rows : Lean.RArray RawFactoredCell) (i : Nat) : Bool :=
  let r:=rows.get i
  @decide (RowSpec pBase qBase pCount qCount pValue qValue pEntries qEntries r)
    (rowSpecDecidable pBase qBase pCount qCount pValue qValue pEntries qEntries r) &&
    decide (i=0 → r.n=pBase) &&
    decide (if i+1 < count then r.next=(rows.get (i+1)).n else r.next=stop)

noncomputable def checkRows (pBase qBase pCount qCount pValue qValue stop count : Nat)
    (pEntries qEntries : Lean.RArray PrimeWindow.Entry) (rows : Lean.RArray RawFactoredCell) : Bool :=
  decide (0 < count) && allFrom (checkRow pBase qBase pCount qCount pValue qValue stop count pEntries qEntries rows) 0 count

lemma row_counts {pBase qBase pCount qCount pValue qValue primeCount : Nat}
    {primes : Lean.RArray Nat} {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {r : RawFactoredCell}
    (pRun : SourceExecution pBase pValue) (qRun : SourceExecution qBase qValue)
    (good : ∀ j, j < primeCount → Nat.Prime (primes.get j))
    (pChecked : PrimeWindow.checkAll pBase primes primeCount pEntries pCount=true)
    (qChecked : PrimeWindow.checkAll qBase primes primeCount qEntries qCount=true)
    (spec : RowSpec pBase qBase pCount qCount pValue qValue pEntries qEntries r) :
    SourceExecution (r.next-1) r.P ∧ SourceExecution r.j r.Q := by
  obtain ⟨pn,step,pend,qn,qend,pval,qval,lu,je,ac,strict,lo,hi,logval,m2,mhi,j2,jhi⟩ := spec
  have po : r.next-1-pBase ≤ pCount := by omega
  have qo : r.j-qBase ≤ qCount := by omega
  have pm : pBase+(r.next-1-pBase)=r.next-1 := by omega
  have qm : qBase+(r.j-qBase)=r.j := by omega
  have pc := count_offset good pChecked po
  have qc := count_offset good qChecked qo
  rw [pm,source_execution_count pRun] at pc
  rw [qm,source_execution_count qRun] at qc
  exact ⟨QuotientCountRealization.source_execution_from_kernel_value m2 mhi (pc.trans pval.symm),
    QuotientCountRealization.source_execution_from_kernel_value j2 jhi (qc.trans qval.symm)⟩

lemma row_real_enclosures {pBase qBase pCount qCount pValue qValue : Nat}
    {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {r : RawFactoredCell}
    (spec : RowSpec pBase qBase pCount qCount pValue qValue pEntries qEntries r) :
    (r.toCell eLo eHi).Enclosures := by
  obtain ⟨pn,step,pend,qn,qend,pval,qval,lu,je,ac,strict,lo,hi,logval,m2,mhi,j2,jhi⟩ := spec
  have he := finite_e_enclosure
  rw [finiteELow_value] at he
  have helo : (eLo:ℝ) ≤ Real.exp 1*(2:ℝ)^60 :=
    (div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^60)).mp he.1
  have hehi : Real.exp 1*(2:ℝ)^60 ≤ (eHi:ℝ) :=
    (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^60)).mp he.2
  have hlog := binaryLogUpper_sound (n:=r.n) (two:=2^35) (k:=35) rfl lo hi
  rw [←logval] at hlog
  have hlogScaled := (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^40)).mp hlog
  have hexp : Real.exp 1 ≤ (r.n:ℝ) := by
    have lower : (2:ℝ)^35 ≤ (r.n:ℝ) := by exact_mod_cast lo
    linarith [Real.exp_one_lt_d9]
  exact r.toCell_enclosures eLo eHi hexp helo hehi hlogScaled

lemma row_sound {pBase qBase pCount qCount pValue qValue primeCount : Nat}
    {primes : Lean.RArray Nat} {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {r : RawFactoredCell}
    (pRun : SourceExecution pBase pValue) (qRun : SourceExecution qBase qValue)
    (good : ∀ j, j < primeCount → Nat.Prime (primes.get j))
    (pChecked : PrimeWindow.checkAll pBase primes primeCount pEntries pCount=true)
    (qChecked : PrimeWindow.checkAll qBase primes primeCount qEntries qCount=true)
    (spec : RowSpec pBase qBase pCount qCount pValue qValue pEntries qEntries r) :
    (r.toCell eLo eHi).FixedPredicate ∧ (r.toCell eLo eHi).CountsCorrect ∧ (r.toCell eLo eHi).Enclosures := by
  have counts := row_counts pRun qRun good pChecked qChecked spec
  obtain ⟨pn,step,pend,qn,qend,pval,qval,lu,je,ac,strict,lo,hi,logval,m2,mhi,j2,jhi⟩ := spec
  exact ⟨r.toCell_fixedPredicate eLo eHi step lu je ac strict,
    r.toCell_counts eLo eHi (source_execution_count counts.1) (source_execution_count counts.2),
    row_real_enclosures ⟨pn,step,pend,qn,qend,pval,qval,lu,je,ac,strict,lo,hi,logval,m2,mhi,j2,jhi⟩⟩

/-- Generic indexed adjacency creates the ORIGINAL network chain object. -/
lemma raw_chain_range (rows : Nat → RawFactoredCell) (count : Nat) :
    ∀ offset,
      (∀ i, offset ≤ i → i < offset+count → (rows i).n < (rows i).next) →
      (∀ i, offset ≤ i → i < offset+count → (rows i).next=(rows (i+1)).n) →
      RawCellChain (rows offset).n (rows (offset+count)).n ((List.range' offset count).map rows) := by
  induction count with
  | zero => intro offset strict adjacent; simpa using RawCellChain.nil (rows offset).n
  | succ count ih =>
    intro offset strict adjacent
    simp only [List.range'_succ,List.map_cons]
    apply RawCellChain.cons (rows offset) (strict offset (by omega) (by omega))
    rw [adjacent offset (by omega) (by omega)]
    have rest := ih (offset+1) (fun i low high=>strict i (by omega) (by omega))
      (fun i low high=>adjacent i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest

#print axioms row_sound
#print axioms raw_chain_range
end RamanujanPV.WindowCells
