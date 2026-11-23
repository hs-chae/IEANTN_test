import OcticLogEndpointData
namespace RHOcticPush.Moments.Endpoint
open Real LeanCert.Core LeanCert.Engine LeanCert.Validity
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem logRow_sound {i : Nat} (verified : logRow i=true) :
    log (grid i:ℝ) ≤ (logUpper i:ℝ) := by
  by_cases hi : i=0
  · subst i
    have h : (0:ℚ) ≤ logUpper 0 := by
      simpa only [logRow,ite_true,decide_eq_true_eq] using verified
    have hr : (0:ℝ) ≤ (logUpper 0:ℝ) := Rat.cast_nonneg.mpr h
    simpa [grid] using hr
  · have hh : checkUpperBound (.log (.var 0)) (point (grid i)) (logUpper i) cfg=true := by
      simpa only [logRow,if_neg hi] using verified
    have mem : (grid i:ℝ) ∈ point (grid i) := by simp [IntervalRat.mem_def,point]
    have h := verify_upper_bound (.log (.var 0)) (.log (.var 0))
      (point (grid i)) (logUpper i) cfg hh (grid i) mem
    simpa only [Expr.eval] using h

#print axioms logRow_sound
end RHOcticPush.Moments.Endpoint
