/- Actual source-produced point intervals supply the actual C-weight coefficient
functions, without replacing their high words by a separate recorded table. -/
import SynergyHeightC.MainWeightData
import SourceHeightPointsV2.OutputFamily
import SynergyAnalytic.EndpointAnyWidth
namespace SynergyHeightC.MainWeightModel
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem source_point_caps (source : SourcePointOutputFamily)
    (domains : ∀ i < logCellCount, cellDomain i=true) :
    EndpointHeightCaps heightEndpoint pointC pointD logCellCount := by
  intro i hi
  obtain ⟨hl,hr,hm,hd⟩ := domain_spec (i:=i) (domains i hi)
  obtain ⟨base,input,c,d,hinput,hmodel,hsource⟩ := source i hi
  have sameInput : input=gridInput (i+1) := Option.some.inj (hinput.symm.trans hr)
  have hsameModel : modelOutputs input=some (modelPair i) :=
    (congrArg modelOutputs sameInput).trans hm
  have sameOutputs : (c,d)=modelPair i := Option.some.inj (hmodel.symm.trans hsameModel)
  have sameC : realWord c.hi=pointC i :=
    congrArg (fun pair : ProofBox × ProofBox=>realWord pair.1.hi) sameOutputs
  have sameD : realWord d.hi=pointD i :=
    congrArg (fun pair : ProofBox × ProofBox=>realWord pair.2.hi) sameOutputs
  have hinputReal := logCell_sound (Nat.succ_le_of_lt hi) hinput
  obtain ⟨rank,after,actualSource,readC,readD,containsC,containsD⟩ :=
    source_output_enclosures (base:=base) (input:=input)
      (c:=c) (d:=d) (x:=logEndpoint (i+1)) hsource hmodel hinputReal
  have mainBound : r184 (logEndpoint (i+1)) ≤ realWord c.hi :=
    (le_div_iff₀ (RealBox.scale_real_pos 128)).mpr containsC.2
  have slopeBound : r186 (logEndpoint (i+1)) ≤ realWord d.hi :=
    (le_div_iff₀ (RealBox.scale_real_pos 128)).mpr containsD.2
  rw [sameC] at mainBound
  rw [sameD] at slopeBound
  rw [point_main_exact (logEndpoint_pos (i+1))] at mainBound
  rw [point_slope_exact] at slopeBound
  exact ⟨by simpa only [heightEndpoint] using mainBound,
    by simpa only [heightEndpoint] using slopeBound,
    (domain_D (i:=i) (domains i hi)).1⟩


theorem source_actual_height_caps (source : SourcePointOutputFamily)
    (domains : ∀ i < logCellCount, cellDomain i=true)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height) :
    ActualHeightCaps heightEndpoint fullC pointD logCellCount := by
  have hc := endpoint_any_width_actual_height_caps (a:=heightEndpoint) (c:=pointC)
    (D:=pointD) (n:=logCellCount) heightEndpoint_monotone
    heightEndpoint_zero heightEndpoint_last h (source_point_caps source domains) hRH
  have hC : (fun i=>pointC i+21600)=fullC :=
    funext (fun i=>(fullC_eq i).symm)
  rw [hC] at hc
  exact hc

#print axioms source_point_caps
#print axioms source_actual_height_caps
end SynergyHeightC.MainWeightModel
