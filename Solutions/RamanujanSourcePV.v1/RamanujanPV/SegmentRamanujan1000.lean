/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.SegmentTableProvider
import RamanujanPV.CriticalSourceClosed

/-! Actual segmented checker on the selected Ramanujan proof path. The original
two base source counts, accepted local classifications, eight scalar rows and
real enclosures are unchanged. Every needed subsequent count is derived through
the complete actual segmented C execution and positive_output_sound, before it
is transported to the original IEANTN CompleteCertificate consumer. -/
namespace RamanujanPV.SegmentRamanujan1000
open QuotientCCell WindowCells SegmentWindowCells
set_option autoImplicit false

theorem p_provider : CountProvider 38358837683 1000 1644673232 LocalWindow1000B.pEntries :=
  SegmentTableProvider.source_provider CriticalSourceClosed.p_source
    (LocalPrimeTree.bounded_prime_provider LocalWindow1000B.primes_good LocalWindow1000B.primeCount)
    LocalWindow1000B.p_checked (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [QuotientDriverSource.capacity])

theorem q_provider : CountProvider 14111427770 369 632207037 LocalWindow1000B.qEntries :=
  SegmentTableProvider.source_provider CriticalSourceClosed.q_source
    (LocalPrimeTree.bounded_prime_provider LocalWindow1000B.primes_good LocalWindow1000B.primeCount)
    LocalWindow1000B.q_checked (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [QuotientDriverSource.capacity])

theorem complete_certificate : CompleteCertificate 38358837683 38358838684
    ((rawList LocalCells1000.rows LocalCells1000.rowCount).map (fun r=>r.toCell eLo eHi)) :=
  SegmentWindowCells.complete_certificate p_provider q_provider LocalCells1000.checked

/-- Every real point, including all noninteger points between the eight source-
checked cells. There is no finite positivity or endpoint count assumption. -/
theorem first_1001_real_interval {x : ℝ}
    (lower : (38358837683:ℝ) ≤ x) (upper : x < 38358838684) : Holds x :=
  complete_certificate_sound complete_certificate x lower upper

#print axioms p_provider
#print axioms q_provider
#print axioms complete_certificate
#print axioms first_1001_real_interval
end RamanujanPV.SegmentRamanujan1000
