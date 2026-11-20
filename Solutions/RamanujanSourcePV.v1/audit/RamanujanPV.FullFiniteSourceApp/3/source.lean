/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FullFiniteScalars
import RamanujanPV.FiniteLogUpperExecute
import RamanujanPV.FiniteWideExpEnclosures
import RamanujanPV.FiniteCellProtected

/-! Additional input applicability for the ORIGINAL full scalar records.
The old Spec and accepted proofs are preserved. The extra clauses are checked
independently, especially A=floor, which does not follow from the old A bound.
No primality/count correctness or Ramanujan conclusion is claimed here. -/
namespace RamanujanPV.FullFiniteSourcePV
open FullFiniteScalars WindowCells QuotientDemandCheck
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Exactly seven source argument bounds and four additional non-strict guards. -/
def AppSpec (r : RawFactoredCell) : Prop :=
  r.n<2^64 ∧r.next<2^64 ∧r.j<2^64 ∧r.P<2^64 ∧r.Q<2^64 ∧r.Lu<2^64 ∧r.A<2^64 ∧
  r.j≤r.n ∧r.Q≤r.j ∧r.P≤r.next-1 ∧r.A=(r.n*eLo)/r.Lu

instance appDecidable (r : RawFactoredCell) : Decidable (AppSpec r) := by
  unfold AppSpec
  infer_instance

def checkApp (r : RawFactoredCell) : Bool := decide (AppSpec r)

structure Applicability (r : RawFactoredCell) : Prop where
  words : FiniteCellProtected.WordFits r
  jBound : r.j≤r.n
  qBound : r.Q≤r.j
  pBound : r.P≤r.next-1
  aFloor : r.A=(r.n*eLo)/r.Lu

theorem app_clauses {r : RawFactoredCell} (h : AppSpec r) : Applicability r := by
  obtain ⟨nw,xw,jw,pw,qw,lw,aw,jb,qb,pb,af⟩:=h
  exact ⟨⟨nw,xw,jw,pw,qw,lw,aw⟩,jb,qb,pb,af⟩

theorem checked_app {r : RawFactoredCell} (h : checkApp r=true) : Applicability r :=
  app_clauses (of_decide_eq_true h)

/-- The accepted normalization/value identity is transported through the WHOLE
actual C logarithm, all20 source iterations and source-closed ceil/series calls. -/
theorem log_source {e : FullFiniteScalars.Entry} (spec : Spec e) :
    FiniteLogUpperExecute.SourceExecution e.row.n e.row.Lu := by
  obtain ⟨low,step,upper,lu,je,ac,strict,normLow,normHigh,value⟩:=spec
  exact FiniteLogUpperExecute.source_execution_from_math (by omega) (by omega)
    rfl normLow normHigh value

/-- Real enclosures now use actual e and generic actual log source outputs. -/
theorem source_enclosures {e : FullFiniteScalars.Entry} (spec : Spec e) :
    (e.row.toCell eLo eHi).Enclosures := by
  have eBounds:=FiniteWideExpEnclosures.source_e_scaled FiniteWideExpEnclosures.actual_source_e_outputs
  have logBound:=FiniteLogUpperExecute.source_log_upper_sound (log_source spec)
  have scaled : Real.log (e.row.n:ℝ)*(2:ℝ)^40≤(e.row.Lu:ℝ) :=
    (le_div_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^40)).mp logBound
  have hn : Real.exp 1≤(e.row.n:ℝ) := by
    have lower : (38358837683:ℝ)≤(e.row.n:ℝ) := by exact_mod_cast spec.1
    linarith [Real.exp_one_lt_d9]
  exact e.row.toCell_enclosures eLo eHi hn eBounds.1 eBounds.2 scaled

/-- Coverage only, with no use of the old scalar/enclosure soundness theorem. -/
theorem checked_chain {start stop count : Nat} {rows : Lean.RArray FullFiniteScalars.Entry}
    (positive : 0<count)
    (checked : allFrom (checkOne start stop count rows) 0 count=true) :
    RawCellChain start stop (rawRows rows count) := by
  have each : ∀i,i<count→Spec (rows.get i) ∧ (i=0→(rows.get i).row.n=start) ∧
      (if i+1<count then (rows.get i).row.next=(rows.get (i+1)).row.n else (rows.get i).row.next=stop) := by
    intro i hi
    exact clauses (allFrom_at count 0 checked i (by omega) (by omega))
  let extended : Nat→RawFactoredCell:=fun i=>if i<count then (rows.get i).row else boundaryRow stop
  have step : ∀ i, 0 ≤ i → i < 0+count → (extended i).n < (extended i).next := by
    intro i low hi
    have bound : i<count := by omega
    simpa [extended,bound] using (each i bound).1.2.1
  have adjacent : ∀ i, 0 ≤ i → i < 0+count → (extended i).next=(extended (i+1)).n := by
    intro i low hi
    have bound : i<count := by omega
    have h:=(each i bound).2.2
    by_cases next : i+1<count
    · rw [if_pos next] at h
      simpa [extended,bound,next] using h
    · rw [if_neg next] at h
      simpa [extended,bound,next,boundaryRow] using h
  have chain:=raw_chain_range extended count 0 step adjacent
  have listEq : (List.range' 0 count).map extended=rawRows rows count := by
    unfold rawRows
    rw [List.range_eq_range']
    apply List.map_congr_left
    intro i hi
    have bound : i<count := by simpa using hi
    simp [extended,bound]
  rw [listEq] at chain
  have first : (extended 0).n=start := by
    simpa [extended,positive] using (each 0 positive).2.1 rfl
  have last : (extended (0+count)).n=stop := by simp [extended,boundaryRow]
  rw [first,last] at chain
  exact chain

#print axioms checked_chain
#print axioms checked_app
#print axioms log_source
#print axioms source_enclosures
end RamanujanPV.FullFiniteSourcePV
