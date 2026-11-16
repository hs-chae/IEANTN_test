/- Pure exact arithmetic for both statistics using already kernel-proved C-model
high words. This module imports no C execution proof and makes no native call. -/
import SourceMomentWordsV1.All
import SynergyBasis.PositiveDivision
namespace SynergyMomentMath.Cells
open ScopedNumerical SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
noncomputable section
inductive Stat where
 | mass
 | firstMoment
 deriving DecidableEq

def weight (left right : ProofBox) : ProofBox := SynergyBasis.Positive.positiveSub
  (SynergyBasis.Positive.expNeg left) (SynergyBasis.Positive.expNeg right)
def term (stat : Stat) (left right : ProofBox) (cWord dWord : Int) : ProofBox :=
  let mass := ProofBox.mul 128 (ProofBox.literal 128 2 1)
    (ProofBox.mul 128 (weight left right) ⟨cWord,cWord⟩)
  match stat with
  | .mass => mass
  | .firstMoment => ProofBox.mul 128 mass ⟨dWord,dWord⟩
def cell (stat : Stat) (i : Nat) : Option ProofBox := do
 let left ← logCell i
 let right ← logCell (i+1)
 let words := SourceMomentWordsV1.All.word i
 pure (term stat left right words.1 words.2)
def sum (stat : Stat) (count : Nat) : Option ProofBox :=
 (List.range count).foldlM (fun total i=>do
   let next ← cell stat i
   pure (ProofBox.add total next)) (⟨0,0⟩ : ProofBox)
structure Row where
 index : Nat
 before : ProofBox
 after : ProofBox
 deriving DecidableEq

def checkValue (value : Option ProofBox) (before after : ProofBox) : Bool :=
 match value with
 | none=>false
 | some next=>decide (ProofBox.add before next=after)
theorem checkValue_sound {value : Option ProofBox} {before after : ProofBox}
 (h : checkValue value before after=true) :
 ∃ next,value=some next ∧ ProofBox.add before next=after := by
 cases value with
 | none=>simp [checkValue] at h
 | some next=>exact ⟨next,rfl,of_decide_eq_true h⟩
def check (stat : Stat) (row : Row) : Bool :=
 checkValue (cell stat row.index) row.before row.after
theorem check_sound {stat : Stat} {row : Row} (h : check stat row=true) :
 ∃ value,cell stat row.index=some value ∧ ProofBox.add row.before value=row.after :=
 checkValue_sound h
#print axioms check_sound
end
end SynergyMomentMath.Cells
