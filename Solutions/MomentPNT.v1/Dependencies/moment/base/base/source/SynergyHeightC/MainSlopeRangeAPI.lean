/- Translate newly checked bounds on the unchanged actual C point model to the
same coefficient function consumed by the PNT theorem. -/
import SynergyHeightC.MainWeightData
namespace SynergyHeightC.MainSlopeRangeAPI
open ScopedNumerical SynergyAnalytic SynergyAnalytic.HeightPoint
open SynergyHeightC.MainWeightModel SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem from_all (xs : List Int)
    (checked : xs.all (fun z=>decide
      (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true)
    (z : Int) (member : z∈xs) :
    77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128 :=
  of_decide_eq_true ((List.all_eq_true.mp checked) z member)

theorem real_range (z : Int)
    (bounds : 77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128) :
    77 ≤ realWord z ∧ realWord z ≤ 163 := by
  have hs := SynergyBasis.RealBox.scale_real_pos 128
  constructor
  · apply (le_div_iff₀ hs).mpr
    exact_mod_cast bounds.1
  · apply (div_le_iff₀ hs).mpr
    exact_mod_cast bounds.2

theorem from_outputs {i : Nat} (checked : cellDomain i=true)
    {input : ProofBox} {pair : ProofBox × ProofBox}
    (ht : logCell (i+1)=some input)
    (hm : modelOutputs input=some pair)
    (bounds : 77*ProofBox.scale 128 ≤ pair.2.hi ∧
      pair.2.hi ≤ 163*ProofBox.scale 128) :
    77 ≤ pointD i ∧ pointD i ≤ 163 := by
  obtain ⟨hl,hr,hm0,hdomain⟩ := domain_spec (i:=i) checked
  have sameInput : input=gridInput (i+1) := Option.some.inj (ht.symm.trans hr)
  have hsame : modelOutputs input=some (modelPair i) :=
    (congrArg modelOutputs sameInput).trans hm0
  have samePair : pair=modelPair i := Option.some.inj (hm.symm.trans hsame)
  have sameD : realWord pair.2.hi=pointD i :=
    congrArg (fun p : ProofBox × ProofBox=>realWord p.2.hi) samePair
  rw [←sameD]
  exact real_range pair.2.hi bounds

#print axioms from_all
#print axioms real_range
#print axioms from_outputs
end SynergyHeightC.MainSlopeRangeAPI
