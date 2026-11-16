/- Pure generic fold correspondence. Function parameters prevent symbolic
normalization from executing the concrete numerical evaluator. -/
import SynergyHeightC.MainWeightFold
namespace SynergyHeightC.MainBudgetFoldGeneric
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

def sum (get : Nat → Option ProofBox) (n : Nat) : Option ProofBox :=
  (List.range n).foldlM (MainWeightModel.addCell get) ⟨0,0⟩

theorem sum_next (get : Nat → Option ProofBox) (n : Nat) :
    sum get (n+1)=(do
      let previous ← sum get n
      let value ← get n
      pure (ProofBox.add previous value)) := by
  unfold sum
  rw [List.range_succ,List.foldlM_append]
  cases h : (List.range n).foldlM (MainWeightModel.addCell get) (⟨0,0⟩ : ProofBox) with
  | none => rfl
  | some previous =>
      simp only [h,Bind.bind,Option.bind,List.foldlM_cons,List.foldlM_nil,
        MainWeightModel.addCell]
      cases get n <;> rfl

theorem sum_of_recurrence (get : Nat → Option ProofBox) (totals : Nat → ProofBox)
    (zero : totals 0=⟨0,0⟩)
    (steps : ∀ i, i < 768 → ∃ value, get i=some value ∧
      ProofBox.add (totals i) value=totals (i+1))
    (n : Nat) (bound : n ≤ 768) : sum get n=some (totals n) := by
  induction n with
  | zero => rw [zero]; rfl
  | succ n ih =>
      obtain ⟨value,cell,next⟩ := steps n (by omega)
      rw [sum_next get n,ih (by omega)]
      simp only [Bind.bind,Option.bind,cell,Pure.pure,next]

theorem actual_sum_function_exact : MainWeightModel.prefixSum=sum MainWeightModel.cell := by
  have shift : (fun j=>MainWeightModel.cell (0+j))=MainWeightModel.cell := by
    funext j
    rw [Nat.zero_add]
  change (fun n=>(List.range n).foldlM
      (MainWeightModel.addCell (fun j=>MainWeightModel.cell (0+j))) ⟨0,0⟩)=
    (fun n=>(List.range n).foldlM (MainWeightModel.addCell MainWeightModel.cell) ⟨0,0⟩)
  exact congrArg (fun get=>fun n=>(List.range n).foldlM
    (MainWeightModel.addCell get) (⟨0,0⟩ : ProofBox)) shift

#print axioms sum_of_recurrence
#print axioms actual_sum_function_exact
end SynergyHeightC.MainBudgetFoldGeneric
