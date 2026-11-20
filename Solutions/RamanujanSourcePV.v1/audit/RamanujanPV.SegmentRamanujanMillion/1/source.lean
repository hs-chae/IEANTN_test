/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.SegmentTableProvider
import RamanujanPV.CriticalSourceClosed
import RamanujanPV.LocalCellsMillion.Final

/-! Actual segmented checker on the selected Ramanujan proof path. The original
two base source counts, accepted local classifications, 285 scalar rows and
real enclosures are unchanged. Every needed subsequent count is derived through
the complete actual segmented C execution and positive_output_sound, before it
is transported to the original IEANTN CompleteCertificate consumer. -/
namespace RamanujanPV.SegmentRamanujanMillion
open QuotientCCell WindowCells SegmentWindowCells
set_option autoImplicit false

theorem p_provider : CountProvider 38358837683 1000000 1644673232 LocalWindowMillion.pEntries :=
  SegmentTableProvider.source_provider CriticalSourceClosed.p_source
    (LocalPrimeTree.bounded_prime_provider LocalWindowMillion.primes_good LocalWindowMillion.primeCount)
    LocalWindowMillion.p_checked (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [QuotientDriverSource.capacity])

theorem q_provider : CountProvider 14111427770 367880 632207037 LocalWindowMillion.qEntries :=
  SegmentTableProvider.source_provider CriticalSourceClosed.q_source
    (LocalPrimeTree.bounded_prime_provider LocalWindowMillion.primes_good LocalWindowMillion.primeCount)
    LocalWindowMillion.q_checked (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [QuotientDriverSource.capacity])

theorem complete_certificate : CompleteCertificate 38358837683 38359837684
    ((rawList LocalCellsMillion.rows LocalCellsMillion.rowCount).map (fun r=>r.toCell eLo eHi)) :=
  SegmentWindowCells.complete_certificate p_provider q_provider LocalCellsMillion.checked

/-- Every real point, including all noninteger points between the285 source-
checked cells. There is no finite positivity or endpoint count assumption. -/
theorem first_1000001_real_interval {x : ℝ}
    (lower : (38358837683:ℝ) ≤ x) (upper : x < 38359837684) : Holds x :=
  complete_certificate_sound complete_certificate x lower upper

#print axioms p_provider
#print axioms q_provider
#print axioms complete_certificate
#print axioms first_1000001_real_interval
end RamanujanPV.SegmentRamanujanMillion
