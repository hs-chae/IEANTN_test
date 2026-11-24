import SpectralRamProfile
import SpectralRamFrontier

/-! Independent interface probes. The numerical cell bodies are imported from
their accepted development objects, not re-evaluated by this review. -/
open Real IEANTN

example (profile : RHPrimeCounting.v5.compensation_profile)
    (table : Buthe.v1.table_1_interval_bounds)
    (lower : Buthe.v1.theorem_2_li_minus_pi)
    (upper : Buthe.v1.theorem_2_li_gt_pi)
    (x : ℝ) (start : (606000000000 : ℝ) ≤ x) (stop : x ≤ 610000000000) :
    (1 / 1000 : ℝ) * x ^ 2 / (log x) ^ 6 ≤ RamanujanGap.v1.gap x :=
  RHOcticPush.SpectralRam.local_actual_gap profile table lower upper start stop

example (x : ℝ) (start : (610000000000 : ℝ) ≤ x) :
    RHOcticPush.SpectralRam.frontier606 x = RHOcticPush.Correlated.strongFrontier607 x :=
  RHOcticPush.SpectralRam.preserves_strong_profile start

example (x : ℝ) (start : (640000000000 : ℝ) ≤ x) :
    RHOcticPush.SpectralRam.frontier606 x = RHContinuation.Ramanujan.finalMargin x :=
  RHOcticPush.SpectralRam.retains_full_original start

#check @RHOcticPush.SpectralRam.actual_frontier606
#check @RHOcticPush.SpectralRam.actual_gap606
#check @RHOcticPush.SpectralRam.actual_strict606
#print axioms RHOcticPush.SpectralRam.local_actual_gap
#print axioms RHOcticPush.SpectralRam.bridge606_from_profile
#print axioms RHOcticPush.SpectralRam.actual_frontier606
#print axioms RHOcticPush.SpectralRam.actual_gap606
#print axioms RHOcticPush.SpectralRam.actual_strict606
