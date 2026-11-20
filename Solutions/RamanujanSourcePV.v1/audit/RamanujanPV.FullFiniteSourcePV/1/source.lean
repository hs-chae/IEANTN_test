/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FullFiniteSourceApp
import RamanujanPV.FiniteCellGeneric
import RamanujanPV.CertificateMargin

/-! Actual unchanged C source on every original finite scalar row. The old
mathematical record identities are reused to instantiate the generic, fully
source-closed e/log/cell program proofs. No source counter output or prime-count
truth is introduced. -/
namespace RamanujanPV.FullFiniteSourcePV
open FullFiniteScalars WindowCells QuotientDemandCheck
set_option autoImplicit false
set_option maxHeartbeats 0

structure RowSource (r : RawFactoredCell) : Prop where
  domain : FiniteCellGeneric.Domain r
  actual : FiniteCellGeneric.SourceExecution r
  fixed : (r.toCell eLo eHi).FixedPredicate
  enclosures : (r.toCell eLo eHi).Enclosures

theorem row_source {e : FullFiniteScalars.Entry} (spec : Spec e) (app : Applicability e.row) :
    RowSource e.row := by
  have logarithm:=log_source spec
  have enclosure:=source_enclosures spec
  obtain ⟨low,step,upper,lu,je,ac,strict,normLow,normHigh,value⟩:=spec
  have domain : FiniteCellGeneric.Domain e.row :=
    ⟨app.words,low,step,by omega,app.jBound,app.qBound,app.pBound,lu,je,app.aFloor,logarithm⟩
  have actual:=FiniteCellGeneric.source_execution_from_math domain strict
  have sourceStrict:=FiniteCellGeneric.positive_implies_strict domain actual
  exact ⟨domain,actual,e.row.toCell_fixedPredicate eLo eHi step lu je
    (FinitePredicateBounds.floor_relation app.aFloor) sourceStrict,enclosure⟩

/-- Explicit scalar/source witness, deliberately excluding CountsCorrect. -/
def SourceScalarCertificate (start stop : Nat) (rows : List RawFactoredCell) : Prop :=
  RawCellChain start stop rows ∧∀r∈rows,RowSource r

def SourceMarginCertificate (start stop D : Nat) (rows : List RawFactoredCell) : Prop :=
  SourceScalarCertificate start stop rows ∧∀r∈rows,Margin r D

theorem checked_block_source {start stop count D : Nat} {rows : Lean.RArray FullFiniteScalars.Entry}
    (positive : 0<count)
    (checked : allFrom (checkOne start stop count rows) 0 count=true)
    (extra : allFrom (fun i=>checkAppMargin (rows.get i).row D) 0 count=true) :
    SourceMarginCertificate start stop D (rawRows rows count) := by
  refine ⟨⟨checked_chain positive checked,?_⟩,?_⟩
  · intro r member
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp member
    have bound:=List.mem_range.mp hi
    have spec:=(clauses (allFrom_at count 0 checked i (by omega) (by omega))).1
    have app:=checked_app (app_margin_clauses (allFrom_at count 0 extra i (by omega) (by omega))).1
    exact row_source spec app
  · intro r member
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp member
    have bound:=List.mem_range.mp hi
    exact (app_margin_clauses (allFrom_at count 0 extra i (by omega) (by omega))).2

theorem append_source_certificate {a b c : Nat} {xs ys : List RawFactoredCell}
    (left : SourceScalarCertificate a b xs) (right : SourceScalarCertificate b c ys) :
    SourceScalarCertificate a c (xs++ys) := by
  refine ⟨append_chain left.1 right.1,?_⟩
  intro r member
  rcases List.mem_append.mp member with h|h
  · exact left.2 r h
  · exact right.2 r h

theorem append_source_margin_certificate {a b c D : Nat} {xs ys : List RawFactoredCell}
    (left : SourceMarginCertificate a b D xs) (right : SourceMarginCertificate b c D ys) :
    SourceMarginCertificate a c D (xs++ys) := by
  refine ⟨append_source_certificate left.1 right.1,?_⟩
  intro r member
  rcases List.mem_append.mp member with h|h
  · exact left.2 r h
  · exact right.2 r h

theorem erase_source {start stop : Nat} {rows : List RawFactoredCell}
    (source : SourceScalarCertificate start stop rows) : ScalarCertificate start stop rows :=
  ⟨source.1,fun r hr=>⟨(source.2 r hr).fixed,(source.2 r hr).enclosures⟩⟩

/-- Missing actual source count outputs remain an explicit mathematical input. -/
theorem complete_from_source_counts {start stop : Nat} {rows : List RawFactoredCell}
    (source : SourceScalarCertificate start stop rows)
    (counts : ∀r∈rows,QuotientCCell.SourceExecution (r.next-1) r.P ∧QuotientCCell.SourceExecution r.j r.Q) :
    CompleteCertificate start stop (rows.map (fun r=>r.toCell eLo eHi)) :=
  FullFiniteScalars.complete_from_counts (erase_source source)
    (fun r hr=>⟨QuotientCCell.source_execution_count (counts r hr).1,
      QuotientCCell.source_execution_count (counts r hr).2⟩)

/-- The retained stronger integer margin becomes a real gap bound ONLY once
all missing actual source count executions have been completed. -/
theorem gap_from_source_counts {start stop D : Nat} {rows : List RawFactoredCell}
    (source : SourceMarginCertificate start stop D rows)
    (counts : ∀r∈rows,QuotientCCell.SourceExecution (r.next-1) r.P ∧QuotientCCell.SourceExecution r.j r.Q) :
    ∀x:ℝ,(start:ℝ)≤x→x<(stop:ℝ)→(D:ℝ)<gap x :=
  CertificateMargin.list_certificate (complete_from_source_counts source.1 counts)
    (fun r hr=>FinitePredicateBounds.floor_relation (source.1.2 r hr).domain.aFloor) source.2

#print axioms row_source
#print axioms checked_block_source
#print axioms complete_from_source_counts
#print axioms gap_from_source_counts
end RamanujanPV.FullFiniteSourcePV
