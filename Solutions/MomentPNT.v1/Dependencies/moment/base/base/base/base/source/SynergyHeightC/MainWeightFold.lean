/- Grouping the exact model's integer additions changes no numerical algorithm. -/
import SynergyHeightC.MainWeightModel
namespace SynergyHeightC.MainWeightModel
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem add_assoc (a b c : ProofBox) :
    ProofBox.add (ProofBox.add a b) c = ProofBox.add a (ProofBox.add b c) := by
  cases a; cases b; cases c
  simp [ProofBox.add,Int.add_assoc]

theorem zero_add (a : ProofBox) : ProofBox.add ⟨0,0⟩ a = a := by
  cases a
  simp [ProofBox.add]

def addCell (get : Nat → Option ProofBox) (total : ProofBox) (i : Nat) : Option ProofBox := do
  let x ← get i
  pure (ProofBox.add total x)

theorem fold_shift (get : Nat → Option ProofBox) (indices : List Nat) (start : ProofBox) :
    indices.foldlM (addCell get) start =
      (indices.foldlM (addCell get) (⟨0,0⟩ : ProofBox)).map (ProofBox.add start) := by
  induction indices generalizing start with
  | nil =>
      cases start
      simp [List.foldlM,ProofBox.add]
  | cons i tail ih =>
      simp only [List.foldlM_cons]
      cases hg : get i with
      | none => simp [addCell,hg]
      | some x =>
          simp only [addCell,hg,Bind.bind,Option.bind,Pure.pure]
          rw [ih (ProofBox.add start x),ih (ProofBox.add ⟨0,0⟩ x)]
          cases hr : tail.foldlM (addCell get) (⟨0,0⟩ : ProofBox) with
          | none => simp [hr]
          | some y => simp [hr,add_assoc,zero_add]

theorem block_add (lo a b : Nat) :
    block lo (a+b) = (do
      let x ← block lo a
      let y ← block (lo+a) b
      pure (ProofBox.add x y)) := by
  unfold block
  rw [List.range_add,List.foldlM_append]
  simp_rw [List.foldlM_map]
  change ((List.range a).foldlM (addCell (fun j=>cell (lo+j))) ⟨0,0⟩ >>= fun x=>
    (List.range b).foldlM (addCell (fun j=>cell (lo+(a+j)))) x) =
    ((List.range a).foldlM (addCell (fun j=>cell (lo+j))) ⟨0,0⟩ >>= fun x=>
      (List.range b).foldlM (addCell (fun j=>cell ((lo+a)+j))) ⟨0,0⟩ >>= fun y=>
        some (ProofBox.add x y))
  simp only [←Nat.add_assoc]
  cases h : (List.range a).foldlM (addCell (fun j=>cell (lo+j))) (⟨0,0⟩ : ProofBox) with
  | none => rfl
  | some x =>
      simp only [Bind.bind,Option.bind]
      rw [fold_shift]
      cases (List.range b).foldlM (addCell (fun j=>cell ((lo+a)+j)))
        (⟨0,0⟩ : ProofBox) <;> rfl

def chunked : Nat → Option ProofBox
  | 0 => some ⟨0,0⟩
  | n+1 => do
      let x ← chunked n
      let y ← block (32*n) 32
      pure (ProofBox.add x y)

theorem block_eq_chunked (n : Nat) : block 0 (32*n)=chunked n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.mul_succ,block_add,ih]
      simp only [Nat.zero_add,chunked]

theorem domain_of_block {lo i : Nat}
    (checked : ((List.range 32).all (fun j=>cellDomain (lo+j)))=true)
    (lower : lo ≤ i) (upper : i < lo+32) : cellDomain i=true := by
  have hj : i-lo < 32 := by omega
  have h := List.all_eq_true.mp checked (i-lo) (List.mem_range.mpr hj)
  simpa only [Nat.add_sub_of_le lower] using h

#print axioms fold_shift
#print axioms block_add
#print axioms block_eq_chunked
#print axioms domain_of_block
end SynergyHeightC.MainWeightModel
