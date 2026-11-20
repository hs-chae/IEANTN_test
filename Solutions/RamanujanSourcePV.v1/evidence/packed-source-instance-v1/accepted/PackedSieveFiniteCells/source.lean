/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteProgramCells
namespace RamanujanPV.PackedSieveFiniteCells
open WindowCells FiniteProgramCells QuotientDemandCheck
set_option autoImplicit false
set_option maxHeartbeats 0

def chainCheck (start stop count : Nat) (rows : Lean.RArray RawFactoredCell) (i : Nat) : Bool :=
  decide (i=0→(rows.get i).n=start) &&
  decide (if i+1<count then (rows.get i).next=(rows.get (i+1)).n else (rows.get i).next=stop)
def layoutCheck (start stop count : Nat) (rows : Lean.RArray RawFactoredCell) : Bool :=
  decide (0<count) && allFrom (chainCheck start stop count rows) 0 count

theorem complete_certificate {start stop count : Nat} {rows : Lean.RArray RawFactoredCell}
    (checked : layoutCheck start stop count rows=true)
    (counts : ∀i,i<count→QuotientCCell.SourceExecution ((rows.get i).next-1) (rows.get i).P ∧
      QuotientCCell.SourceExecution (rows.get i).j (rows.get i).Q)
    (domains : Domains rows count) (actual : Executions rows count) (logs : Logs rows count) :
    CompleteCertificate start stop ((rawList rows count).map (fun r=>r.toCell eLo eHi)) := by
  have parts : 0<count ∧ allFrom (chainCheck start stop count rows) 0 count=true := by
    simpa [layoutCheck] using checked
  have each : ∀i,i<count→(i=0→(rows.get i).n=start) ∧
      (if i+1<count then (rows.get i).next=(rows.get (i+1)).n else (rows.get i).next=stop) := by
    intro i hi
    simpa only [chainCheck, Bool.and_eq_true, decide_eq_true_eq] using
      allFrom_at count 0 parts.2 i (by omega) (by omega)
  let extended : Nat→RawFactoredCell:=fun i=>if i<count then rows.get i else boundaryRow stop
  have step : ∀ (i : Nat), (0 ≤ i) → (i < 0+count) → (extended i).n < (extended i).next := by
    intro i _ hi
    simpa [extended,show i<count by omega] using (domains i (by omega)).advance
  have adjacent : ∀ (i : Nat), (0 ≤ i) → (i < 0+count) →
      (extended i).next = (extended (i+1)).n := by
    intro i _ hi
    have bound : i<count := by omega
    have h:=(each i bound).2
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
  have first : (extended 0).n=start := by simpa [extended,parts.1] using (each 0 parts.1).1 rfl
  have last : (extended (0+count)).n=stop := by simp [extended,boundaryRow]
  rw [first,last] at chain
  refine ⟨chain.toCellChain eLo eHi,?_⟩
  intro c hc
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hc
  change r∈(List.range count).map rows.get at hr
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hr
  have index:=List.mem_range.mp hi
  have pair:=counts i index
  have domain:=domains i index
  have strict:=FiniteCellProtected.positive_implies_strict domain (actual i index)
  exact ⟨(rows.get i).toCell_fixedPredicate eLo eHi domain.advance domain.logPositive domain.jExp
      (FinitePredicateBounds.floor_relation domain.aFloor) strict,
    (rows.get i).toCell_counts eLo eHi (QuotientCCell.source_execution_count pair.1)
      (QuotientCCell.source_execution_count pair.2),row_enclosures domain (logs i index)⟩
#print axioms complete_certificate
end RamanujanPV.PackedSieveFiniteCells
