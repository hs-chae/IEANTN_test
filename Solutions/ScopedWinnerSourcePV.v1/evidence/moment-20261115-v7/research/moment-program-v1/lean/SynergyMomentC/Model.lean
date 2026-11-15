/- The exact added C entry's interval expressions and their real meanings.
Finite numerical/source-loop/output providers are still separate obligations. -/
import SynergyMomentC.SourceBindings
import SynergyHeightC.MainWeightData
namespace SynergyMomentC.Model
open ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
open SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

def massTerm (left right c : ProofBox) : ProofBox :=
  ProofBox.mul 128 (ProofBox.literal 128 2 1)
    (ProofBox.mul 128 (weight left right) (fc c))
def term (kind : Kind) (left right c d : ProofBox) : ProofBox :=
  match kind with
  | .mass => massTerm left right c
  | .firstMoment => ProofBox.mul 128 (massTerm left right c) (fd d)
def cell (kind : Kind) (i : Nat) : Option ProofBox := do
  let left ← logCell i
  let right ← logCell (i+1)
  let pair ← SynergyHeightC.PointExecuteAPI.modelOutputs right
  pure (term kind left right pair.1 pair.2)
def block (kind : Kind) (lo count : Nat) : Option ProofBox :=
  (List.range count).foldlM (fun total j => do
    let next ← cell kind (lo+j)
    pure (ProofBox.add total next)) (⟨0,0⟩ : ProofBox)
def prefixSum (kind : Kind) (count : Nat) : Option ProofBox := block kind 0 count

noncomputable def realMass (i : Nat) : ℝ :=
  2*((1/heightEndpoint i-1/heightEndpoint (i+1))*fullC i)
noncomputable def realMoment (i : Nat) : ℝ := realMass i*pointD i
noncomputable def realTerm (kind : Kind) (i : Nat) : ℝ :=
  match kind with | .mass => realMass i | .firstMoment => realMoment i

theorem mass_term_sound {left right c : ProofBox} {u v : ℝ}
    (hl : RealBox.Contains 128 left u) (hr : RealBox.Contains 128 right v)
    (hu : 0 ≤ u) (hu64 : u ≤ 64) (hv : 0 ≤ v) (hv64 : v ≤ 64) (ordered : u ≤ v) :
    RealBox.Contains 128 (massTerm left right c)
      (2*((Real.exp (-u)-Real.exp (-v))*realWord (adjustedC c).hi)) := by
  exact RealBox.mul_sound (literal_integer_sound 2)
    (RealBox.mul_sound (weight_sound hl hr hu hu64 hv hv64 ordered)
      (exact_word_sound (adjustedC c).hi))

theorem moment_term_sound {left right c d : ProofBox} {u v : ℝ}
    (hl : RealBox.Contains 128 left u) (hr : RealBox.Contains 128 right v)
    (hu : 0 ≤ u) (hu64 : u ≤ 64) (hv : 0 ≤ v) (hv64 : v ≤ 64) (ordered : u ≤ v) :
    RealBox.Contains 128 (term .firstMoment left right c d)
      ((2*((Real.exp (-u)-Real.exp (-v))*realWord (adjustedC c).hi))*realWord d.hi) := by
  exact RealBox.mul_sound (mass_term_sound hl hr hu hu64 hv hv64 ordered)
    (exact_word_sound d.hi)

def highPair (pair : ProofBox × ProofBox) : Int × Int :=
  ((adjustedC pair.1).hi,pair.2.hi)
def termFromWords (kind : Kind) (left right : ProofBox) (cWord dWord : Int) : ProofBox :=
  let mass := ProofBox.mul 128 (ProofBox.literal 128 2 1)
    (ProofBox.mul 128 (weight left right) ⟨cWord,cWord⟩)
  match kind with
  | .mass => mass
  | .firstMoment => ProofBox.mul 128 mass ⟨dWord,dWord⟩

theorem term_from_high_words (kind : Kind) (left right c d : ProofBox)
    {cWord dWord : Int} (cHigh : (adjustedC c).hi=cWord) (dHigh : d.hi=dWord) :
    term kind left right c d=termFromWords kind left right cWord dWord := by
  cases kind <;> simp only [term,massTerm,termFromWords,fc,fd,cHigh,dHigh]

#print axioms mass_term_sound
#print axioms moment_term_sound
#print axioms term_from_high_words
end SynergyMomentC.Model
