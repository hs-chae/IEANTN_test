import LiSeriesDerivative
import FinalResult
namespace RHContinuation.Ramanujan
open Real IEANTN RamanujanPV.AnalyticTransition
/-- The actual all-real Ramanujan theorem now uses seven explicit inputs.
The separate derivative identity is proved from the retained li series bridge. -/
theorem ramanujan_640b_seven_inputs (hRH : SharedRH.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    (hs : LogIntegralSeriesIdentity IEANTN.li)
    {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    (1/25:ℝ) ≤ RamStudy.RG x :=
  Ramanujan640.ramanujan_640b hRH hT hJ hL hU hS hs
    (li_derivative_from_series hs) hx

#print axioms ramanujan_640b_seven_inputs
#check @ramanujan_640b_seven_inputs
end RHContinuation.Ramanujan
