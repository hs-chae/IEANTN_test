/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FullFiniteSourcePV
import RamanujanPV.FullAdaptiveScalars.Block0000Check
namespace RamanujanPV.FullAdaptiveSourcePV.Block0000
open QuotientDemandCheck FullFiniteScalars FullFiniteSourcePV
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def appCheck (i : Nat) : Bool := checkAppMargin (RamanujanPV.FullAdaptiveScalars.Block0000.rows.get i).row 9005
theorem part_0000 : allFrom appCheck 0 32=true := by decide +kernel
#print axioms part_0000
theorem union_0000 : allFrom appCheck 0 32=true := part_0000
theorem paired_checked : allFrom appCheck 0 RamanujanPV.FullAdaptiveScalars.Block0000.count=true := union_0000
theorem certificate : SourceMarginCertificate RamanujanPV.FullAdaptiveScalars.Block0000.start RamanujanPV.FullAdaptiveScalars.Block0000.stop 9005 (rawRows RamanujanPV.FullAdaptiveScalars.Block0000.rows RamanujanPV.FullAdaptiveScalars.Block0000.count) := checked_block_source (by decide) RamanujanPV.FullAdaptiveScalars.Block0000.checked paired_checked
#print axioms paired_checked
#print axioms certificate
end RamanujanPV.FullAdaptiveSourcePV.Block0000
