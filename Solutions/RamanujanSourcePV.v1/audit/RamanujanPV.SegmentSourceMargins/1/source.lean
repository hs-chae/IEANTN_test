/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.SegmentRamanujanMillion
import RamanujanPV.CertificateMargin
import RamanujanPV.CriticalWindowMargin

/-! Quantitative margins retain the provenance of the supplied ACTUAL
segmented-source certificates. No parallel cardinality count path is used. -/
namespace RamanujanPV.SegmentSourceMargins
open QuotientDemandCheck
set_option autoImplicit false

theorem million_margins_checked : allFrom
    (WindowMargin.check LocalCellsMillion.rows 501901) 0 285=true := by
  decide +kernel

theorem million_gap {x : ℝ}
    (lower : (38358837683:ℝ) ≤ x) (upper : x < 38359837684) :
    (501901:ℝ) < gap x :=
  CertificateMargin.checked_array_certificate SegmentRamanujanMillion.complete_certificate
    LocalCellsMillion.checked million_margins_checked x lower upper

theorem thousand_gap {x : ℝ}
    (lower : (38358837683:ℝ) ≤ x) (upper : x < 38358838684) :
    (52869788:ℝ) < gap x :=
  CertificateMargin.checked_array_certificate SegmentRamanujan1000.complete_certificate
    LocalCells1000.checked CriticalWindowMargin.margins_checked x lower upper

#print axioms million_margins_checked
#print axioms million_gap
#print axioms thousand_gap
end RamanujanPV.SegmentSourceMargins
