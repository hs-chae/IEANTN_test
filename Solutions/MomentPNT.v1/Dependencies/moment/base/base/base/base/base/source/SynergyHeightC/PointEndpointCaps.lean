/- Source-derived endpoint caps. The outstanding execution obligations are explicit
   in SourcePointChecks; no completed application-PV claim is made here. -/
import SynergyHeightC.PointModelEnclosures
import SynergyAnalytic.HeightPointWordBounds
namespace SynergyHeightC.PointExecuteAPI
open ScopedC ScopedNumerical ScopedNumerical.ProofBox
open SynergyBasis SynergyBasis.Positive SynergyAnalytic SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The exact original 768 RIGHT-endpoint input boxes. The default is never
used on a successful point check, as the source-derived bounds theorem proves. -/
def pointInput (i : Nat) : ProofBox := (logCell (i+1)).getD ⟨0,0⟩

/-- Actual C pointHeight executions, with output-buffer and full-frame checks.
This is a finite proof obligation, not an analytic assumption or a result oracle. -/
def SourcePointChecks (base : Machine.State) : Prop :=
  ∀ i < logCellCount, checkedModel base (pointInput i) = true

/-- The upper caps are proved for the SAME records read from the actual C
output pointers. The source execution is consumed through the output-enclosure
bridge, before the endpoint-count/PNT transfer. -/
theorem source_checked_point_bounds {base : Machine.State} {i : Nat}
    (hi : i < logCellCount)
    (hsource : checkedModel base (pointInput i) = true)
    (hwords : genericPointCheck (logCell (i+1)) (point constantValues)
      (cWords[i]?) (DWords[i]?) mainIndex slopeIndex = true) :
    continuousMain (3681/10000) (3599/10000) (373/200) (1273/2000)
      (129/250) (7/8) (heightEndpoint (i+1)) ≤ baseC i ∧
    continuousSlope (3599/10000) (373/200) (1273/2000) (129/250)
      (heightEndpoint (i+1)) ≤ baseD i ∧ 0 ≤ baseD i := by
  obtain ⟨input,values,c,d,cw,dw,ht,hv,hc,hd,hcw,hdw,hcmp⟩ :=
    genericPointCheck_decode hwords
  have hout : modelOutputs input = some (c,d) := by
    simp only [modelOutputs,hv,hc,hd,Bind.bind,Option.bind,Pure.pure]
  have hin : pointInput i = input := by simp only [pointInput,ht,Option.getD_some]
  rw [hin] at hsource
  have hchecked : checked base input c d = true := by
    simpa only [checkedModel,hout] using hsource
  have hinput := logCell_sound (Nat.succ_le_of_lt hi) ht
  obtain ⟨after,actualSource,readC,readD,containsC,containsD⟩ :=
    source_and_model_enclosures hchecked hout hinput
  have hcR : (c.hi:ℝ) ≤ (cw:ℝ) := by exact_mod_cast hcmp.1
  have hdR : (d.hi:ℝ) ≤ (dw:ℝ) := by exact_mod_cast hcmp.2.1
  have mainBound : r184 (logEndpoint (i+1)) ≤ (cw:ℝ)/(scale p:ℝ) :=
    (le_div_iff₀ (RealBox.scale_real_pos p)).mpr (containsC.2.trans hcR)
  have slopeBound : r186 (logEndpoint (i+1)) ≤ (dw:ℝ)/(scale p:ℝ) :=
    (le_div_iff₀ (RealBox.scale_real_pos p)).mpr (containsD.2.trans hdR)
  rw [point_main_exact (logEndpoint_pos (i+1))] at mainBound
  rw [point_slope_exact] at slopeBound
  refine ⟨?_,?_,?_⟩
  · simpa only [heightEndpoint,baseC,hcw,Option.getD_some] using mainBound
  · simpa only [heightEndpoint,baseD,hdw,Option.getD_some] using slopeBound
  · have hw : (0:ℝ) ≤ (dw:ℝ) := by exact_mod_cast hcmp.2.2
    simpa only [baseD,hdw,Option.getD_some] using
      div_nonneg hw (RealBox.scale_real_pos p).le

theorem source_endpoint_caps {base : Machine.State}
    (hsource : SourcePointChecks base)
    (hwords : ∀ i < logCellCount, genericPointCheck (logCell (i+1))
      (point constantValues) (cWords[i]?) (DWords[i]?) mainIndex slopeIndex = true) :
    EndpointHeightCaps heightEndpoint baseC baseD logCellCount := by
  intro i hi
  exact source_checked_point_bounds hi (hsource i hi) (hwords i hi)

#print axioms source_checked_point_bounds
#print axioms source_endpoint_caps
end SynergyHeightC.PointExecuteAPI
