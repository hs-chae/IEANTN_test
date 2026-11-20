/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveQueries
import RamanujanPV.PackedSieveFiniteCells
import RamanujanPV.FiniteScalarMillion.DomainFinal
import RamanujanPV.FiniteScalarMillion.CellFinal
import RamanujanPV.FiniteScalarMillion.LogFinal
import RamanujanPV.CertificateMargin
namespace RamanujanPV.PackedSieveMillion
open WindowCells FiniteProgramCells PackedSieveFiniteCells
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem layout_checked : layoutCheck 38358837683 38359837684 285 LocalCellsMillion.rows=true := by
  decide +kernel

theorem margins_checked : QuotientDemandCheck.allFrom
    (WindowMargin.check LocalCellsMillion.rows 501901) 0 285=true := by
  decide +kernel

theorem complete_certificate : CompleteCertificate 38358837683 38359837684
    ((rawList LocalCellsMillion.rows LocalCellsMillion.rowCount).map (fun r => r.toCell eLo eHi)) :=
  PackedSieveFiniteCells.complete_certificate layout_checked PackedSieveQueries.row_source_counts
    FiniteScalarMillion.all_cell_domains FiniteScalarMillion.all_cell_source FiniteScalarMillion.all_log_source

theorem first_1000001_real_interval {x : ℝ}
    (lower : (38358837683:ℝ)≤x) (upper : x<38359837684) : Holds x :=
  complete_certificate_sound complete_certificate x lower upper

theorem uniform_gap {x : ℝ}
    (lower : (38358837683:ℝ)≤x) (upper : x<38359837684) : (501901:ℝ)<gap x := by
  apply CertificateMargin.array_certificate complete_certificate _
    margins_checked x lower upper
  intro i hi
  exact FinitePredicateBounds.floor_relation (FiniteScalarMillion.all_cell_domains i hi).aFloor
#print axioms complete_certificate
#print axioms first_1000001_real_interval
#print axioms uniform_gap
end RamanujanPV.PackedSieveMillion
