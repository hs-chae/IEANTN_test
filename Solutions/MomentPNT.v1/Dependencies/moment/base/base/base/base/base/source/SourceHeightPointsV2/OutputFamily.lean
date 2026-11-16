/- Exact source-output caps, independent of the evaluator implementation. -/
import SynergyHeightC.PointSemanticCaps
namespace SynergyHeightC.PointExecuteAPI
open ScopedC ScopedC.Machine ScopedNumerical ScopedNumerical.ProofBox
open SynergyBasis SynergyBasis.Positive SynergyAnalytic SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Actual source-output states may vary with the main-loop index and total.
Each cell still identifies the SAME actual pointer records with its model boxes. -/
def SourcePointOutputFamily : Prop :=
 ∀ i < logCellCount, ∃ base input c d,
  logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
  SourcePointOutputs base input c d

theorem family_point_bounds {i : Nat}
    (hi : i < logCellCount) (source : SourcePointOutputFamily)
    (words : genericPointCheck (logCell (i+1)) (point constantValues)
      (cWords[i]?) (DWords[i]?) mainIndex slopeIndex = true) :
    continuousMain (3681/10000) (3599/10000) (373/200) (1273/2000)
      (129/250) (7/8) (heightEndpoint (i+1)) ≤ baseC i ∧
    continuousSlope (3599/10000) (373/200) (1273/2000) (129/250)
      (heightEndpoint (i+1)) ≤ baseD i ∧ 0 ≤ baseD i := by
  obtain ⟨input,values,c,d,cw,dw,ht,hv,hc,hd,hcw,hdw,hcmp⟩ :=
    genericPointCheck_decode words
  have hm : modelOutputs input = some (c,d) := by
    simp only [modelOutputs,hv,hc,hd,Bind.bind,Option.bind,Pure.pure]
  obtain ⟨actualBase,sourceInput,sourceC,sourceD,hinput,hmodel,hsource⟩ := source i hi
  have sameInput : sourceInput = input := Option.some.inj (hinput.symm.trans ht)
  subst sourceInput
  have sameOutputs : (sourceC,sourceD) = (c,d) := Option.some.inj (hmodel.symm.trans hm)
  obtain ⟨sameC,sameD⟩ := Prod.mk.inj sameOutputs
  subst sourceC
  subst sourceD
  have hinputReal := logCell_sound (Nat.succ_le_of_lt hi) ht
  obtain ⟨rank,after,actualSource,readC,readD,containsC,containsD⟩ :=
    source_output_enclosures hsource hm hinputReal
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

theorem family_endpoint_caps (source : SourcePointOutputFamily)
    (words : ∀ i < logCellCount, genericPointCheck (logCell (i+1))
      (point constantValues) (cWords[i]?) (DWords[i]?) mainIndex slopeIndex = true) :
    EndpointHeightCaps heightEndpoint baseC baseD logCellCount := by
  intro i hi
  exact family_point_bounds hi source (words i hi)

#print axioms family_point_bounds
#print axioms family_endpoint_caps
end SynergyHeightC.PointExecuteAPI
