/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FullAdaptiveScalars.Block0000Data
namespace RamanujanPV.FullAdaptiveScalars.Block0000
open QuotientDemandCheck FullFiniteScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem part_0000 : allFrom rowCheck 0 32=true := by decide +kernel
#print axioms part_0000
theorem union_0000 : allFrom rowCheck 0 32=true := part_0000
theorem checked : allFrom rowCheck 0 count=true := union_0000
theorem certificate : ScalarCertificate start stop (rawRows rows count) := checked_block (by decide) checked
#print axioms checked
#print axioms certificate
end RamanujanPV.FullAdaptiveScalars.Block0000
