import SynergyAnalytic.HeightPointWordBounds
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive VectorExpr
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem checked_point_bounds {i:Nat} (hi:i<logCellCount) (hcheck:genericPointCheck (logCell (i+1)) (point constantValues) (cWords[i]?) (DWords[i]?) mainIndex slopeIndex=true) :
    continuousMain (3681/10000) (3599/10000) (373/200) (1273/2000) (129/250) (7/8) (heightEndpoint (i+1)) ≤ baseC i ∧
    continuousSlope (3599/10000) (373/200) (1273/2000) (129/250) (heightEndpoint (i+1)) ≤ baseD i ∧ 0 ≤ baseD i := by
  obtain ⟨t,vs,c,D,cw,dw,ht,hv,hc,hd,hcw,hdw,hcmp⟩:=genericPointCheck_decode hcheck
  have htmem:=logCell_sound (Nat.succ_le_of_lt hi) ht
  have henv:=(point_sound htmem hv).2
  have hmain:=env_upper_at henv hc (main_real_output (logEndpoint (i+1))) hcmp.1
  have hslope:=env_upper_at henv hd (slope_real_output (logEndpoint (i+1))) hcmp.2.1
  rw [point_main_exact (logEndpoint_pos (i+1))] at hmain
  rw [point_slope_exact] at hslope
  refine ⟨?_,?_,?_⟩
  · simpa only [heightEndpoint,baseC,hcw,Option.getD_some] using hmain
  · simpa only [heightEndpoint,baseD,hdw,Option.getD_some] using hslope
  · have hw : (0:ℝ) ≤ (dw:ℝ) := by exact_mod_cast hcmp.2.2
    simpa only [baseD,hdw,Option.getD_some] using div_nonneg hw (RealBox.scale_real_pos p).le

theorem endpoint_caps_of_all_checks (h:∀i<logCellCount,genericPointCheck (logCell (i+1)) (point constantValues) (cWords[i]?) (DWords[i]?) mainIndex slopeIndex=true) :
    EndpointHeightCaps heightEndpoint baseC baseD logCellCount := by
  intro i hi
  exact checked_point_bounds hi (h i hi)

#print axioms checked_point_bounds
#print axioms endpoint_caps_of_all_checks
end SynergyAnalytic.HeightPoint
