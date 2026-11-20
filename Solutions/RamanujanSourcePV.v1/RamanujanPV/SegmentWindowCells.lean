/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.WindowCells

/-! The original IEANTN certificate and real consumer, with each endpoint count
provided by actual verified-source computations. The arithmetic row/adjacency
and analytic-enclosure checks are exactly the existing WindowCells contracts. -/
namespace RamanujanPV.SegmentWindowCells
open QuotientCCell QuotientDemandCheck WindowCells
set_option autoImplicit false
set_option maxHeartbeats 2000000

def CountProvider (base count value : Nat) (entries : Lean.RArray PrimeWindow.Entry) : Prop :=
  ∀offset,offset ≤ count → SourceExecution (base+offset) (value+offsetValue entries offset)

theorem row_counts {pBase qBase pCount qCount pValue qValue : Nat}
    {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {r : RawFactoredCell}
    (p : CountProvider pBase pCount pValue pEntries)
    (q : CountProvider qBase qCount qValue qEntries)
    (spec : RowSpec pBase qBase pCount qCount pValue qValue pEntries qEntries r) :
    SourceExecution (r.next-1) r.P ∧ SourceExecution r.j r.Q := by
  obtain ⟨pn,step,pend,qn,qend,pval,qval,lu,je,ac,strict,lo,hi,logval,m2,mhi,j2,jhi⟩ := spec
  have pm : pBase+(r.next-1-pBase)=r.next-1 := by omega
  have qm : qBase+(r.j-qBase)=r.j := by omega
  have pc := p (r.next-1-pBase) (by omega)
  have qc := q (r.j-qBase) (by omega)
  rw [pm,←pval] at pc
  rw [qm,←qval] at qc
  exact ⟨pc,qc⟩

theorem row_sound {pBase qBase pCount qCount pValue qValue : Nat}
    {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {r : RawFactoredCell}
    (p : CountProvider pBase pCount pValue pEntries)
    (q : CountProvider qBase qCount qValue qEntries)
    (spec : RowSpec pBase qBase pCount qCount pValue qValue pEntries qEntries r) :
    (r.toCell eLo eHi).FixedPredicate ∧ (r.toCell eLo eHi).CountsCorrect ∧
      (r.toCell eLo eHi).Enclosures := by
  have counts := row_counts p q spec
  have enclosures := row_real_enclosures spec
  obtain ⟨pn,step,pend,qn,qend,pval,qval,lu,je,ac,strict,lo,hi,logval,m2,mhi,j2,jhi⟩ := spec
  exact ⟨r.toCell_fixedPredicate eLo eHi step lu je ac strict,
    r.toCell_counts eLo eHi (source_execution_count counts.1) (source_execution_count counts.2),
    enclosures⟩

/-- The unchanged original network object. Prime-count values enter only through
the supplied verified-source providers, not through a separate cardinality proof. -/
theorem complete_certificate {pBase qBase pCount qCount pValue qValue stop count : Nat}
    {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {rows : Lean.RArray RawFactoredCell}
    (p : CountProvider pBase pCount pValue pEntries)
    (q : CountProvider qBase qCount qValue qEntries)
    (checked : checkRows pBase qBase pCount qCount pValue qValue stop count pEntries qEntries rows=true) :
    CompleteCertificate pBase stop ((rawList rows count).map (fun r=>r.toCell eLo eHi)) := by
  have parts : 0 < count ∧
      allFrom (checkRow pBase qBase pCount qCount pValue qValue stop count pEntries qEntries rows) 0 count=true := by
    simpa [checkRows] using checked
  have each : ∀i,i < count → 
      RowSpec pBase qBase pCount qCount pValue qValue pEntries qEntries (rows.get i) ∧
      (i=0 → (rows.get i).n=pBase) ∧
      (if i+1 < count then (rows.get i).next=(rows.get (i+1)).n else (rows.get i).next=stop) := by
    intro i hi
    exact checkRow_clauses (allFrom_at count 0 parts.2 i (by omega) (by omega))
  let extended : Nat → RawFactoredCell := fun i=>if i < count then rows.get i else boundaryRow stop
  have strict : ∀i,0 ≤ i → i < 0+count → (extended i).n < (extended i).next := by
    intro i low hi
    have bound : i < count := by omega
    simpa [extended,bound] using (each i bound).1.2.1
  have adjacent : ∀i,0 ≤ i → i < 0+count → (extended i).next=(extended (i+1)).n := by
    intro i low hi
    have bound : i < count := by omega
    have h := (each i bound).2.2
    by_cases next : i+1 < count
    · rw [if_pos next] at h
      simpa [extended,bound,next] using h
    · rw [if_neg next] at h
      simpa [extended,bound,next,boundaryRow] using h
  have chain := raw_chain_range extended count 0 strict adjacent
  have listEq : (List.range' 0 count).map extended=rawList rows count := by
    unfold rawList
    rw [List.range_eq_range']
    apply List.map_congr_left
    intro i hi
    have bound : i < count := by simpa using hi
    simp [extended,bound]
  rw [listEq] at chain
  have first : (extended 0).n=pBase := by
    simpa [extended,parts.1] using (each 0 parts.1).2.1 rfl
  have last : (extended (0+count)).n=stop := by simp [extended,boundaryRow]
  rw [first,last] at chain
  refine ⟨chain.toCellChain eLo eHi,?_⟩
  intro c hc
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hc
  change r∈(List.range count).map rows.get at hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  exact row_sound p q (each i (List.mem_range.mp hi)).1

theorem holds_window {pBase qBase pCount qCount pValue qValue stop count : Nat}
    {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {rows : Lean.RArray RawFactoredCell}
    (p : CountProvider pBase pCount pValue pEntries)
    (q : CountProvider qBase qCount qValue qEntries)
    (checked : checkRows pBase qBase pCount qCount pValue qValue stop count pEntries qEntries rows=true) :
    ∀x:ℝ,(pBase:ℝ) ≤ x → x < (stop:ℝ) → Holds x :=
  complete_certificate_sound (complete_certificate p q checked)

#print axioms complete_certificate
#print axioms holds_window
end RamanujanPV.SegmentWindowCells
