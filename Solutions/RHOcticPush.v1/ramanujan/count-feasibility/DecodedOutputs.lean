import RamanujanPV.QuotientDemandCheck
import RamanujanPV.QuotientCountRealization

/-! Reuse all mathematically finished nodes of a checked demand certificate.
No cardinality of finished nodes is assumed. A C-function/model execution is
distinct from a physical driver-main/stdout theorem or parser soundness. -/
namespace RHOcticPush.DecodedOutputs
open RamanujanPV RamanujanPV.QuotientDemandCheck
set_option autoImplicit false

theorem all_meanings {nodes : Lean.RArray Entry} {gaps : Lean.RArray Gap}
    {gapCount count : Nat} (hgap : checkGaps gaps gapCount = true)
    (hentries : checkEntries nodes gaps gapCount count = true) :
    ∀ i, i < count → Meaning (nodes.get i) :=
  entries_sound hgap hentries

theorem finished_pi {nodes : Lean.RArray Entry} {gaps : Lean.RArray Gap}
    {gapCount count : Nat} (hgap : checkGaps gaps gapCount = true)
    (hentries : checkEntries nodes gaps gapCount count = true) :
    ∀ i, i < count → (nodes.get i).kind = 2 →
      Nat.primeCounting (nodes.get i).v = (nodes.get i).value :=
  fun _ hi hkind => certificate_pi hgap hentries hi hkind

theorem finished_source_function {nodes : Lean.RArray Entry} {gaps : Lean.RArray Gap}
    {gapCount count : Nat} (hgap : checkGaps gaps gapCount = true)
    (hentries : checkEntries nodes gaps gapCount count = true) :
    ∀ i, i < count → (nodes.get i).kind = 2 →
      2 ≤ (nodes.get i).v → (nodes.get i).v ≤ 2000000000000 →
      QuotientCCell.SourceExecution (nodes.get i).v (nodes.get i).value :=
  fun i hi hkind hlow hhigh =>
    QuotientCountRealization.source_execution_from_kernel_value hlow hhigh
      (finished_pi hgap hentries i hi hkind)

#print axioms all_meanings
#print axioms finished_pi
#print axioms finished_source_function
end RHOcticPush.DecodedOutputs
