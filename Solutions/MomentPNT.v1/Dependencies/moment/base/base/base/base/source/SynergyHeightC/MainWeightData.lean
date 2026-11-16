/- The exact main-weight model's real coefficient functions and domain decoding. -/
import SynergyHeightC.MainWeightReal
import SynergyHeightC.MainWeightDomainGeneric
import SynergyHeightC.MainWeightCellAbstract
import SynergyAnalytic.HeightPointWordBounds
namespace SynergyHeightC.MainWeightModel
open ScopedNumerical SynergyBasis
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

@[irreducible] def gridInput (i : Nat) : ProofBox := (logCell i).getD ⟨0,0⟩
@[irreducible] def modelPair (i : Nat) : ProofBox × ProofBox :=
  (modelOutputs (gridInput (i+1))).getD (⟨0,0⟩,⟨0,0⟩)
theorem gridInput_function_exact : gridInput=
    (fun i=>(logCell i).getD (⟨0,0⟩ : ProofBox)) := by unfold gridInput; rfl
theorem modelPair_function_exact : modelPair=
    (fun i=>(modelOutputs (gridInput (i+1))).getD (⟨0,0⟩,⟨0,0⟩)) := by
  unfold modelPair
  rfl
noncomputable def pointC (i : Nat) : ℝ := realWord (modelPair i).1.hi
noncomputable def fullC (i : Nat) : ℝ := realWord (adjustedC (modelPair i).1).hi
noncomputable def pointD (i : Nat) : ℝ := realWord (modelPair i).2.hi
noncomputable def realTerm (i : Nat) : ℝ :=
  2*((1/heightEndpoint i-1/heightEndpoint (i+1))*fullC i)*
    pairedFactor (pointD i) (1/8) 330


theorem fullC_eq (i : Nat) : fullC i=pointC i+21600 := by
  have hs := RealBox.scale_real_pos 128
  have hLit : ProofBox.literal 128 21600 1 =
      ⟨21600*ProofBox.scale 128,21600*ProofBox.scale 128⟩ := by decide +kernel
  simp only [fullC,pointC,adjustedC,hLit,ProofBox.add,realWord,Int.cast_add,Int.cast_mul,
    Int.cast_ofNat,add_div,mul_div_cancel_right₀ _ hs.ne']


theorem domain_spec {i : Nat} (checked : cellDomain i=true) :
    logCell i=some (gridInput i) ∧
    logCell (i+1)=some (gridInput (i+1)) ∧
    modelOutputs (gridInput (i+1))=some (modelPair i) ∧
    (0 ≤ (gridInput i).lo ∧ (gridInput i).lo ≤ (gridInput i).hi ∧
      (gridInput i).hi ≤ 64*ProofBox.scale 128 ∧
      0 ≤ (gridInput (i+1)).lo ∧ (gridInput (i+1)).lo ≤ (gridInput (i+1)).hi ∧
      (gridInput (i+1)).hi ≤ 64*ProofBox.scale 128 ∧
      0 ≤ (adjustedC (modelPair i).1).hi ∧ 0 ≤ (modelPair i).2.hi ∧
      (modelPair i).2.hi < 330*ProofBox.scale 128 ∧
      0 ≤ (term (gridInput i) (gridInput (i+1)) (modelPair i).1 (modelPair i).2).lo ∧
      (term (gridInput i) (gridInput (i+1)) (modelPair i).1 (modelPair i).2).lo ≤
        (term (gridInput i) (gridInput (i+1)) (modelPair i).1 (modelPair i).2).hi ∧
      (term (gridInput i) (gridInput (i+1)) (modelPair i).1 (modelPair i).2).hi ≤
        ProofBox.scale 128) := by
  obtain ⟨left,right,c,d,hl,hr,hm,hc⟩ := cell_domain_decode checked
  have hleft : gridInput i=left :=
    (congrFun gridInput_function_exact i).trans
      (congrArg (fun opt : Option ProofBox=>opt.getD ⟨0,0⟩) hl)
  have hright : gridInput (i+1)=right :=
    (congrFun gridInput_function_exact (i+1)).trans
      (congrArg (fun opt : Option ProofBox=>opt.getD ⟨0,0⟩) hr)
  have hmodel : modelOutputs (gridInput (i+1))=some (c,d) := by
    rw [hright]
    exact hm
  have hpair : modelPair i=(c,d) :=
    (congrFun modelPair_function_exact i).trans
      (congrArg (fun opt : Option (ProofBox × ProofBox)=>opt.getD (⟨0,0⟩,⟨0,0⟩)) hmodel)
  refine ⟨?_,?_,?_,?_⟩
  · rw [hleft]
    exact hl
  · rw [hright]
    exact hr
  · rw [hpair]
    exact hmodel
  · rw [hleft,hright,hpair]
    exact hc




theorem real_word_range (z : Int) (nonnegative : 0≤z)
    (upper : z<330*ProofBox.scale 128) : 0≤realWord z ∧ realWord z<330 := by
  have hs := RealBox.scale_real_pos 128
  constructor
  · exact div_nonneg (by exact_mod_cast nonnegative) hs.le
  · apply (div_lt_iff₀ hs).mpr
    exact_mod_cast upper

theorem domain_D {i : Nat} (checked : cellDomain i=true) :
    0 ≤ pointD i ∧ pointD i < 330 := by
  have h := (domain_spec checked).2.2.2
  exact real_word_range _ h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1

theorem cell_real_sound {i : Nat} (hi : i < logCellCount)
    (checked : cellDomain i=true) {b : ProofBox} (result : cell i=some b) :
    RealBox.Contains 128 b (realTerm i) := by
  obtain ⟨hl,hr,hm,hd⟩ := domain_spec checked
  have hb : term (gridInput i) (gridInput (i+1)) (modelPair i).1 (modelPair i).2=b := by
    exact Option.some.inj ((cell_from_pair_data hl hr hm).symm.trans result)
  have hlast : logEndpoint logCellCount=60 := by
    have hh := congrArg Real.log heightEndpoint_last
    simpa only [log_heightEndpoint,Real.log_exp] using hh
  have hu64 : logEndpoint i ≤ 64 := by
    have hh := logEndpoint_monotone (Nat.le_of_lt hi)
    rw [hlast] at hh
    linarith
  have hv64 : logEndpoint (i+1) ≤ 64 := by
    have hh := logEndpoint_monotone (Nat.succ_le_of_lt hi)
    rw [hlast] at hh
    linarith
  have hc := term_sound (c:=(modelPair i).1) (logCell_sound (Nat.le_of_lt hi) hl)
    (logCell_sound (Nat.succ_le_of_lt hi) hr) (logEndpoint_pos i).le hu64
    (logEndpoint_pos (i+1)).le hv64 (logEndpoint_monotone (Nat.le_succ i))
    hd.2.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.2.1
  rw [hb] at hc
  simpa only [realTerm,fullC,pointD,heightEndpoint,realWord,Real.exp_neg,one_div] using hc


#print axioms fullC_eq
#print axioms domain_spec
#print axioms domain_D
#print axioms cell_real_sound
end SynergyHeightC.MainWeightModel
