/- Generic arithmetic fold correspondence. This pure module has no C proof imports. -/
import SynergyMomentMath.Cells
namespace SynergyMomentMath.Fold
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
def addCell (get : Nat→Option ProofBox) (total : ProofBox) (i : Nat) : Option ProofBox := do
 let value←get i
 pure (ProofBox.add total value)
def sum (get : Nat→Option ProofBox) (n : Nat) : Option ProofBox :=
 (List.range n).foldlM (addCell get) ⟨0,0⟩
theorem sum_next (get : Nat→Option ProofBox) (n : Nat) :
 sum get (n+1)=(do
  let previous←sum get n
  let value←get n
  pure (ProofBox.add previous value)) := by
 unfold sum
 rw [List.range_succ,List.foldlM_append]
 cases h : (List.range n).foldlM (addCell get) (⟨0,0⟩ : ProofBox) with
 | none=>rfl
 | some previous=>
  simp only [h,Bind.bind,Option.bind,List.foldlM_cons,List.foldlM_nil,addCell]
  cases get n <;> rfl

theorem sum_of_recurrence (get : Nat→Option ProofBox) (totals : Nat→ProofBox)
 (zero : totals 0=⟨0,0⟩) (steps : ∀ i,i < 768→∃ value,get i=some value ∧
  ProofBox.add (totals i) value=totals (i+1)) (n : Nat) (hn : n ≤ 768) :
 sum get n=some (totals n) := by
 induction n with
 | zero=>rw [zero];rfl
 | succ n ih=>
  obtain ⟨value,cell,next⟩:=steps n (by omega)
  rw [sum_next get n,ih (by omega)]
  simp only [Bind.bind,Option.bind,cell,Pure.pure,next]
theorem cell_sum_function (stat : Cells.Stat) : Cells.sum stat=sum (Cells.cell stat) := rfl
#print axioms sum_next
#print axioms sum_of_recurrence
#print axioms cell_sum_function
end
end SynergyMomentMath.Fold
