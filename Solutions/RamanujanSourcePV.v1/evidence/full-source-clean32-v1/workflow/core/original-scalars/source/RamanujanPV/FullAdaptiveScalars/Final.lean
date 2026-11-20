/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FullAdaptiveScalars.Block0000Check
namespace RamanujanPV.FullAdaptiveScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def allRows : List RawFactoredCell := (FullFiniteScalars.rawRows RamanujanPV.FullAdaptiveScalars.Block0000.rows RamanujanPV.FullAdaptiveScalars.Block0000.count)
theorem all_scalars : FullFiniteScalars.ScalarCertificate 38358837683 38358853591 allRows := RamanujanPV.FullAdaptiveScalars.Block0000.certificate
#print axioms all_scalars
end RamanujanPV.FullAdaptiveScalars
