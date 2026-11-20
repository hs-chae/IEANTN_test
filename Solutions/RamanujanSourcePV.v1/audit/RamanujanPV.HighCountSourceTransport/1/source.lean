/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.QuotientCountRealization

/-! Transport at the unchanged analytic transition endpoint. The numerical
prime-count equality is an explicit input here. This module does not claim
that the pending high certificate has completed or proved that equality.
The actual C function, source-owned initialization, helper executions and
source/AST correspondence are the existing verified ones. Physical native
caller/process association remains a separate boundary. -/
namespace RamanujanPV.HighCountSourceTransport
set_option autoImplicit false

/-- Once the exact endpoint count is proved, the existing entire actual source
function realizes that value; no assumed numerical-response service is used. -/
theorem from_exact_count
    (count : Nat.primeCounting 1490000000000 = 55206486339) :
    QuotientCCell.SourceExecution 1490000000000 55206486339 :=
  QuotientCountRealization.source_execution_from_kernel_value
    (by norm_num) (by norm_num) count

/-- Keep the exact C bytes and the SAME AST's completed execution together. -/
theorem source_linked_from_exact_count
    (count : Nat.primeCounting 1490000000000 = 55206486339) :
    LCMSourcePV.RestrictedC.SourceCorresponds
      QuotientCSource.render QuotientCSource.actualSource () ∧
    QuotientCCell.SourceExecution 1490000000000 55206486339 :=
  ⟨QuotientCSource.actual_source_checked, from_exact_count count⟩

/-- Every completed supported source execution agrees with the exact count;
this does not assume that an unverified physical caller executed that model. -/
theorem every_completed_output_from_exact_count
    (count : Nat.primeCounting 1490000000000 = 55206486339)
    {output : Nat} (run : QuotientCCell.SourceExecution 1490000000000 output) :
    output = 55206486339 :=
  (QuotientCCell.source_execution_count run).symm.trans count

#print axioms from_exact_count
#print axioms source_linked_from_exact_count
#print axioms every_completed_output_from_exact_count
end RamanujanPV.HighCountSourceTransport
