import BalancedCountCheck
/-! Generic feasibility proof only; no new large numerical job is launched.
This ordinary kernel checker is not source-first PV. The pure recursor retains
the original high-count numerical-leaf policy of zero axioms. -/
namespace RHOcticPush.PureBalancedCount
open RamanujanPV.QuotientDemandCheck
set_option autoImplicit false
set_option maxHeartbeats 0

def tree (check : Nat → Bool) (depth i : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) check
    (fun d previous j => Bool.and (previous j) (previous (Nat.add j (Nat.pow 2 d)))) depth i

theorem tree_eq (check : Nat → Bool) (depth : Nat) :
    ∀ i, tree check depth i=allFrom check i (Nat.pow 2 depth) := by
  induction depth with
  | zero =>
    intro i
    change check i=(check i &&true)
    exact (Bool.and_true _).symm
  | succ d ih =>
    intro i
    have hp : Nat.pow 2 (d+1)=Nat.pow 2 d+Nat.pow 2 d := by
      change Nat.pow 2 d * 2=Nat.pow 2 d+Nat.pow 2 d
      exact Nat.mul_two _
    calc tree check (d+1) i
        = (tree check d i &&tree check d (i+Nat.pow 2 d)) := rfl
      _ = (allFrom check i (Nat.pow 2 d) &&allFrom check (i+Nat.pow 2 d) (Nat.pow 2 d)) :=
        congrArg₂ Bool.and (ih i) (ih (i+Nat.pow 2 d))
      _ = allFrom check i (Nat.pow 2 d+Nat.pow 2 d) := (BalancedCount.append_pure check _ _ i).symm
      _ = allFrom check i (Nat.pow 2 (d+1)) := congrArg (allFrom check i) hp.symm

theorem tree_sound {check : Nat → Bool} {i depth : Nat}
    (verified : tree check depth i=true) : allFrom check i (Nat.pow 2 depth)=true :=
  (tree_eq check depth i).symm.trans verified

theorem source_32768 {check : Nat → Bool} {i : Nat}
    (verified : tree check 15 i=true) : allFrom check i 32768=true :=
  tree_sound verified

#print axioms tree
#print axioms tree_eq
#print axioms tree_sound
#print axioms source_32768
end RHOcticPush.PureBalancedCount

#print axioms Nat.brecOn
