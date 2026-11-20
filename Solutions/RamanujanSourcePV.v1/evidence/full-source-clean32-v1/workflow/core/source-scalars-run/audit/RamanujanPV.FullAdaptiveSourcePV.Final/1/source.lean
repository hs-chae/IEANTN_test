/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FullAdaptiveSourcePV.Block0000
namespace RamanujanPV.FullAdaptiveSourcePV
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def allRows : List RawFactoredCell := (FullFiniteScalars.rawRows RamanujanPV.FullAdaptiveScalars.Block0000.rows RamanujanPV.FullAdaptiveScalars.Block0000.count)
theorem all_source_margins : FullFiniteSourcePV.SourceMarginCertificate 38358837683 38358853591 9005 allRows := RamanujanPV.FullAdaptiveSourcePV.Block0000.certificate
theorem all_source_scalars : FullFiniteSourcePV.SourceScalarCertificate 38358837683 38358853591 allRows := all_source_margins.1
#print axioms all_source_margins
#print axioms all_source_scalars
end RamanujanPV.FullAdaptiveSourcePV
