/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FullFiniteSourcePV
import RamanujanPV.FullAdaptiveScalars.Block0407Check
namespace RamanujanPV.FullAdaptiveSourcePV.Block0407
open QuotientDemandCheck FullFiniteScalars FullFiniteSourcePV
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def appCheck (i : Nat) : Bool := checkAppMargin (RamanujanPV.FullAdaptiveScalars.Block0407.rows.get i).row 9005
theorem part_0000 : allFrom appCheck 0 512=true := by decide +kernel
#print axioms part_0000
theorem union_0000 : allFrom appCheck 0 512=true := part_0000
theorem part_0001 : allFrom appCheck 512 512=true := by decide +kernel
#print axioms part_0001
theorem union_0001 : allFrom appCheck 0 1024=true := allFrom_append_checked (i:=0) (n:=512) (m:=512) union_0000 part_0001
theorem part_0002 : allFrom appCheck 1024 512=true := by decide +kernel
#print axioms part_0002
theorem union_0002 : allFrom appCheck 0 1536=true := allFrom_append_checked (i:=0) (n:=1024) (m:=512) union_0001 part_0002
theorem part_0003 : allFrom appCheck 1536 512=true := by decide +kernel
#print axioms part_0003
theorem union_0003 : allFrom appCheck 0 2048=true := allFrom_append_checked (i:=0) (n:=1536) (m:=512) union_0002 part_0003
theorem part_0004 : allFrom appCheck 2048 512=true := by decide +kernel
#print axioms part_0004
theorem union_0004 : allFrom appCheck 0 2560=true := allFrom_append_checked (i:=0) (n:=2048) (m:=512) union_0003 part_0004
theorem part_0005 : allFrom appCheck 2560 512=true := by decide +kernel
#print axioms part_0005
theorem union_0005 : allFrom appCheck 0 3072=true := allFrom_append_checked (i:=0) (n:=2560) (m:=512) union_0004 part_0005
theorem part_0006 : allFrom appCheck 3072 512=true := by decide +kernel
#print axioms part_0006
theorem union_0006 : allFrom appCheck 0 3584=true := allFrom_append_checked (i:=0) (n:=3072) (m:=512) union_0005 part_0006
theorem part_0007 : allFrom appCheck 3584 512=true := by decide +kernel
#print axioms part_0007
theorem union_0007 : allFrom appCheck 0 4096=true := allFrom_append_checked (i:=0) (n:=3584) (m:=512) union_0006 part_0007
theorem paired_checked : allFrom appCheck 0 RamanujanPV.FullAdaptiveScalars.Block0407.count=true := union_0007
theorem certificate : SourceMarginCertificate RamanujanPV.FullAdaptiveScalars.Block0407.start RamanujanPV.FullAdaptiveScalars.Block0407.stop 9005 (rawRows RamanujanPV.FullAdaptiveScalars.Block0407.rows RamanujanPV.FullAdaptiveScalars.Block0407.count) := checked_block_source (by decide) RamanujanPV.FullAdaptiveScalars.Block0407.checked paired_checked
#print axioms paired_checked
#print axioms certificate
end RamanujanPV.FullAdaptiveSourcePV.Block0407
