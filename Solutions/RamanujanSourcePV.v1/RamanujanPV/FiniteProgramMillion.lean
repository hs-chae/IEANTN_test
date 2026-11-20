/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteProgramCells
import RamanujanPV.FiniteScalarMillion.DomainFinal
import RamanujanPV.FiniteScalarMillion.CellFinal
import RamanujanPV.FiniteScalarMillion.LogFinal
import RamanujanPV.SegmentRamanujanMillion
import RamanujanPV.SegmentSourceMargins

/-! The selected million-interval result consumes actual C source for EVERY
numerical family: source count/checker, e, log, and seven-field predicate.
Only coverage, count locations and quantitative integer margins use additional
ordinary kernel checks; these checks do not supply the strict cell predicate. -/
namespace RamanujanPV.FiniteProgramMillion
open WindowCells FiniteProgramCells
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem layout_checked : checkLayout 38358837683 14111427770 1000000 367880
    1644673232 632207037 38359837684 285 LocalWindowMillion.pEntries
      LocalWindowMillion.qEntries LocalCellsMillion.rows=true := by
  decide +kernel

theorem domains : Domains LocalCellsMillion.rows 285 := FiniteScalarMillion.all_cell_domains
theorem executions : Executions LocalCellsMillion.rows 285 := FiniteScalarMillion.all_cell_source
theorem logs : Logs LocalCellsMillion.rows 285 := FiniteScalarMillion.all_log_source

/-- Each original row's strict comparison is DERIVED from actual C return1. -/
theorem source_strict (i : Nat) (hi : i<285) :
    2^20*(LocalCellsMillion.rows.get i).P^2<
      (LocalCellsMillion.rows.get i).A*(LocalCellsMillion.rows.get i).Q :=
  FiniteCellProtected.positive_implies_strict (domains i hi) (executions i hi)

theorem complete_certificate : CompleteCertificate 38358837683 38359837684
    ((rawList LocalCellsMillion.rows LocalCellsMillion.rowCount).map (fun r=>r.toCell eLo eHi)) :=
  FiniteProgramCells.complete_certificate SegmentRamanujanMillion.p_provider
    SegmentRamanujanMillion.q_provider layout_checked domains executions logs

theorem first_1000001_real_interval {x : ℝ}
    (lower : (38358837683:ℝ)≤x) (upper : x<38359837684) : Holds x :=
  complete_certificate_sound complete_certificate x lower upper

theorem uniform_gap {x : ℝ}
    (lower : (38358837683:ℝ)≤x) (upper : x<38359837684) : (501901:ℝ)<gap x := by
  apply CertificateMargin.array_certificate complete_certificate _
    SegmentSourceMargins.million_margins_checked x lower upper
  intro i hi
  exact FinitePredicateBounds.floor_relation (domains i hi).aFloor

#print axioms layout_checked
#print axioms source_strict
#print axioms complete_certificate
#print axioms first_1000001_real_interval
#print axioms uniform_gap
end RamanujanPV.FiniteProgramMillion
