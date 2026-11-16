/- A strengthened kernel-only comparator. These mathematical enclosures do not
prove C source execution and must not be called source-first program verification. -/
import SynergyHeightC.MainWeightData
import SynergyHeightC.PointSemanticOutputs
import SynergyAnalytic.EndpointAnyWidth
namespace SynergyHeightC.MainModelOnlyCaps
open ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
open SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem pair_enclosures {input : ProofBox} {pair : ProofBox × ProofBox} {x : ℝ}
    (model : PointExecuteAPI.modelOutputs input=some pair)
    (contains : RealBox.Contains 128 input x) :
    RealBox.Contains 128 pair.1 (r184 x) ∧ RealBox.Contains 128 pair.2 (r186 x) := by
  rcases pair with ⟨c,d⟩
  exact PointExecuteAPI.model_output_enclosures model contains

theorem model_point_caps (domains : ∀ i < logCellCount, cellDomain i=true) :
    EndpointHeightCaps heightEndpoint pointC pointD logCellCount := by
  intro i hi
  obtain ⟨left,right,model,domain⟩ := domain_spec (i:=i) (domains i hi)
  have input := logCell_sound (Nat.succ_le_of_lt hi) right
  have contains := pair_enclosures (input:=gridInput (i+1)) (pair:=modelPair i)
    (x:=logEndpoint (i+1)) model input
  have cBound : r184 (logEndpoint (i+1)) ≤ realWord (modelPair i).1.hi :=
    (le_div_iff₀ (RealBox.scale_real_pos 128)).mpr contains.1.2
  have dBound : r186 (logEndpoint (i+1)) ≤ realWord (modelPair i).2.hi :=
    (le_div_iff₀ (RealBox.scale_real_pos 128)).mpr contains.2.2
  rw [point_main_exact (logEndpoint_pos (i+1))] at cBound
  rw [point_slope_exact] at dBound
  exact ⟨by simpa only [heightEndpoint,pointC] using cBound,
    by simpa only [heightEndpoint,pointD] using dBound,(domain_D (domains i hi)).1⟩

theorem model_actual_height_caps (domains : ∀ i < logCellCount, cellDomain i=true)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height) :
    ActualHeightCaps heightEndpoint fullC pointD logCellCount := by
  have caps := endpoint_any_width_actual_height_caps (a:=heightEndpoint) (c:=pointC)
    (D:=pointD) (n:=logCellCount) heightEndpoint_monotone heightEndpoint_zero
    heightEndpoint_last h (model_point_caps domains) hRH
  have full : (fun i=>pointC i+21600)=fullC := funext (fun i=>(fullC_eq i).symm)
  rw [full] at caps
  exact caps

#print axioms pair_enclosures
#print axioms model_point_caps
#print axioms model_actual_height_caps
end SynergyHeightC.MainModelOnlyCaps
