/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteCellProtected
import RamanujanPV.FiniteWideExpEnclosures
import RamanujanPV.SegmentWindowCells

/-! Source-first cell consumption. Coverage/count-location checks contain NO
strict inequality, e enclosure, logarithm enclosure, or finite positivity.
The actual C return1 proves the integer predicate; actual e/log source outputs
and actual segmented source outputs prove the remaining original fields. -/
namespace RamanujanPV.FiniteProgramCells
open WindowCells SegmentWindowCells QuotientDemandCheck
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure IndexSpec (pBase qBase pCount qCount pValue qValue : Nat)
    (pEntries qEntries : Lean.RArray PrimeWindow.Entry) (r : RawFactoredCell) : Prop where
  pLower : pBase≤r.n
  pUpper : r.next≤pBase+pCount+1
  qLower : qBase≤r.j
  qUpper : r.j≤qBase+qCount
  pValue : r.P=pValue+offsetValue pEntries (r.next-1-pBase)
  qValue : r.Q=qValue+offsetValue qEntries (r.j-qBase)

noncomputable instance indexSpecDecidable (pBase qBase pCount qCount pValue qValue : Nat)
    (pEntries qEntries : Lean.RArray PrimeWindow.Entry) (r : RawFactoredCell) :
    Decidable (IndexSpec pBase qBase pCount qCount pValue qValue pEntries qEntries r) := by
  exact decidable_of_iff
    (pBase≤r.n ∧ r.next≤pBase+pCount+1 ∧ qBase≤r.j ∧ r.j≤qBase+qCount ∧
      r.P=pValue+offsetValue pEntries (r.next-1-pBase) ∧
      r.Q=qValue+offsetValue qEntries (r.j-qBase))
    ⟨fun ⟨a,b,c,d,e,f⟩=>⟨a,b,c,d,e,f⟩,fun h=>⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩⟩

noncomputable def checkIndex (pBase qBase pCount qCount pValue qValue stop count : Nat)
    (pEntries qEntries : Lean.RArray PrimeWindow.Entry) (rows : Lean.RArray RawFactoredCell) (i : Nat) : Bool :=
  decide (IndexSpec pBase qBase pCount qCount pValue qValue pEntries qEntries (rows.get i)) &&
  decide (i=0→(rows.get i).n=pBase) &&
  decide (if i+1<count then (rows.get i).next=(rows.get (i+1)).n else (rows.get i).next=stop)

noncomputable def checkLayout (pBase qBase pCount qCount pValue qValue stop count : Nat)
    (pEntries qEntries : Lean.RArray PrimeWindow.Entry) (rows : Lean.RArray RawFactoredCell) : Bool :=
  decide (0<count) && allFrom (checkIndex pBase qBase pCount qCount pValue qValue stop count pEntries qEntries rows) 0 count

lemma index_clauses {pBase qBase pCount qCount pValue qValue stop count i : Nat}
    {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {rows : Lean.RArray RawFactoredCell}
    (checked : checkIndex pBase qBase pCount qCount pValue qValue stop count pEntries qEntries rows i=true) :
    IndexSpec pBase qBase pCount qCount pValue qValue pEntries qEntries (rows.get i) ∧
      (i=0→(rows.get i).n=pBase) ∧
      (if i+1<count then (rows.get i).next=(rows.get (i+1)).n else (rows.get i).next=stop) := by
  unfold checkIndex at checked
  have h : decide (IndexSpec pBase qBase pCount qCount pValue qValue pEntries qEntries (rows.get i))=true ∧
      decide (i=0→(rows.get i).n=pBase)=true ∧
      decide (if i+1<count then (rows.get i).next=(rows.get (i+1)).n else (rows.get i).next=stop)=true := by
    simpa only [Bool.and_eq_true,and_assoc] using checked
  exact ⟨of_decide_eq_true h.1,of_decide_eq_true h.2.1,of_decide_eq_true h.2.2⟩

def Domains (rows : Lean.RArray RawFactoredCell) (count : Nat) : Prop :=
  ∀i,i<count→FiniteCellProtected.Domain (rows.get i)
def Executions (rows : Lean.RArray RawFactoredCell) (count : Nat) : Prop :=
  ∀i,i<count→FiniteCellExecution.SourceExecution (rows.get i)
def Logs (rows : Lean.RArray RawFactoredCell) (count : Nat) : Prop :=
  ∀i,i<count→FiniteLogExecution.SourceExecution (rows.get i).n (rows.get i).Lu

theorem row_counts {pBase qBase pCount qCount pValue qValue : Nat}
    {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {r : RawFactoredCell}
    (p : CountProvider pBase pCount pValue pEntries)
    (q : CountProvider qBase qCount qValue qEntries)
    (index : IndexSpec pBase qBase pCount qCount pValue qValue pEntries qEntries r)
    (domain : FiniteCellProtected.Domain r) :
    QuotientCCell.SourceExecution (r.next-1) r.P ∧ QuotientCCell.SourceExecution r.j r.Q := by
  have hl:=index.pLower
  have hu:=index.pUpper
  have qa:=index.qLower
  have qb:=index.qUpper
  have step:=domain.advance
  have pm : pBase+(r.next-1-pBase)=r.next-1 := by omega
  have qm : qBase+(r.j-qBase)=r.j := by omega
  have pc:=p (r.next-1-pBase) (by omega)
  have qc:=q (r.j-qBase) (by omega)
  rw [pm,←index.pValue] at pc
  rw [qm,←index.qValue] at qc
  exact ⟨pc,qc⟩

theorem row_enclosures {r : RawFactoredCell} (domain : FiniteCellProtected.Domain r)
    (sourceLog : FiniteLogExecution.SourceExecution r.n r.Lu) :
    (r.toCell eLo eHi).Enclosures := by
  have e:=FiniteWideExpEnclosures.source_e_scaled FiniteWideExpEnclosures.actual_source_e_outputs
  have logUpper:=FiniteLogExecution.source_log_upper_sound sourceLog
  have scaled : Real.log (r.n:ℝ)*(2:ℝ)^40≤(r.Lu:ℝ) :=
    (le_div_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^40)).mp logUpper
  have hexp : Real.exp 1≤(r.n:ℝ) := by
    have bound : (38358837683:ℝ)≤(r.n:ℝ) := by exact_mod_cast domain.nLower
    linarith [Real.exp_one_lt_d9]
  exact r.toCell_enclosures eLo eHi hexp e.1 e.2 scaled

theorem row_sound {pBase qBase pCount qCount pValue qValue : Nat}
    {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {r : RawFactoredCell}
    (p : CountProvider pBase pCount pValue pEntries)
    (q : CountProvider qBase qCount qValue qEntries)
    (index : IndexSpec pBase qBase pCount qCount pValue qValue pEntries qEntries r)
    (domain : FiniteCellProtected.Domain r) (actual : FiniteCellExecution.SourceExecution r)
    (sourceLog : FiniteLogExecution.SourceExecution r.n r.Lu) :
    (r.toCell eLo eHi).FixedPredicate ∧ (r.toCell eLo eHi).CountsCorrect ∧
      (r.toCell eLo eHi).Enclosures := by
  have counts:=row_counts p q index domain
  have strict:=FiniteCellProtected.positive_implies_strict domain actual
  have floor:=FinitePredicateBounds.floor_relation domain.aFloor
  exact ⟨r.toCell_fixedPredicate eLo eHi domain.advance domain.logPositive domain.jExp floor strict,
    r.toCell_counts eLo eHi (QuotientCCell.source_execution_count counts.1)
      (QuotientCCell.source_execution_count counts.2), row_enclosures domain sourceLog⟩

theorem complete_certificate {pBase qBase pCount qCount pValue qValue stop count : Nat}
    {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {rows : Lean.RArray RawFactoredCell}
    (p : CountProvider pBase pCount pValue pEntries)
    (q : CountProvider qBase qCount qValue qEntries)
    (checked : checkLayout pBase qBase pCount qCount pValue qValue stop count pEntries qEntries rows=true)
    (domains : Domains rows count) (actual : Executions rows count) (logs : Logs rows count) :
    CompleteCertificate pBase stop ((rawList rows count).map (fun r=>r.toCell eLo eHi)) := by
  have parts : 0<count ∧ allFrom
      (checkIndex pBase qBase pCount qCount pValue qValue stop count pEntries qEntries rows) 0 count=true := by
    simpa [checkLayout] using checked
  have each : ∀i,i<count→IndexSpec pBase qBase pCount qCount pValue qValue pEntries qEntries (rows.get i) ∧
      (i=0→(rows.get i).n=pBase) ∧
      (if i+1<count then (rows.get i).next=(rows.get (i+1)).n else (rows.get i).next=stop) := by
    intro i hi
    exact index_clauses (allFrom_at count 0 parts.2 i (by omega) (by omega))
  let extended : Nat→RawFactoredCell:=fun i=>if i<count then rows.get i else boundaryRow stop
  have step : ∀i,0≤i→i<0+count→(extended i).n<(extended i).next := by
    intro i low hi
    have bound : i<count := by omega
    simpa [extended,bound] using (domains i bound).advance
  have adjacent : ∀i,0≤i→i<0+count→(extended i).next=(extended (i+1)).n := by
    intro i low hi
    have bound : i<count := by omega
    have h:=(each i bound).2.2
    by_cases next : i+1<count
    · rw [if_pos next] at h
      simpa [extended,bound,next] using h
    · rw [if_neg next] at h
      simpa [extended,bound,next,boundaryRow] using h
  have chain:=raw_chain_range extended count 0 step adjacent
  have listEq : (List.range' 0 count).map extended=rawList rows count := by
    unfold rawList
    rw [List.range_eq_range']
    apply List.map_congr_left
    intro i hi
    have bound : i<count := by simpa using hi
    simp [extended,bound]
  rw [listEq] at chain
  have first : (extended 0).n=pBase := by
    simpa [extended,parts.1] using (each 0 parts.1).2.1 rfl
  have last : (extended (0+count)).n=stop := by simp [extended,boundaryRow]
  rw [first,last] at chain
  refine ⟨chain.toCellChain eLo eHi,?_⟩
  intro c hc
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hc
  change r∈(List.range count).map rows.get at hr
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hr
  have index:=List.mem_range.mp hi
  exact row_sound p q (each i index).1 (domains i index) (actual i index) (logs i index)

#print axioms row_sound
#print axioms complete_certificate
end RamanujanPV.FiniteProgramCells
