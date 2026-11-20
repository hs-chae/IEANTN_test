/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.CriticalSourceClosed
import RamanujanPV.WindowMargin

/-! Unconditional uniform quantitative improvement over the whole checked
1,001-real-width window, using the same two original source executions. -/
namespace RamanujanPV.CriticalWindowMargin
open QuotientDemandCheck
set_option autoImplicit false

theorem margins_checked : allFrom
    (WindowMargin.check LocalCells1000.rows 52869788) 0 8=true := by
  decide +kernel

/-- The first-cell margin in fact survives all eight adaptive cells. -/
theorem uniform_gap {x : ℝ}
    (hx : (38358837683:ℝ) ≤ x) (hxNext : x < 38358838684) :
    (52869788:ℝ) < gap x :=
  WindowMargin.quantitative_window CriticalSourceClosed.p_source CriticalSourceClosed.q_source
    (LocalPrimeTree.bounded_prime_provider LocalWindow1000B.primes_good LocalWindow1000B.primeCount)
    LocalWindow1000B.p_checked LocalWindow1000B.q_checked LocalCells1000.checked margins_checked x hx hxNext

#print axioms margins_checked
#print axioms uniform_gap
end RamanujanPV.CriticalWindowMargin
