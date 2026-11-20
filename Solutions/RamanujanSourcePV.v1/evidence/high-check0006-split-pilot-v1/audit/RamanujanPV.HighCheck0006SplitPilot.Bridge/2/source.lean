/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.QuotientDemandCheck
namespace RamanujanPV.HighCheck0006SplitPilot
open QuotientDemandCheck
set_option autoImplicit false
set_option maxHeartbeats 0
private theorem and_assoc_pure (a b c : Bool) : (a&&b)&&c=a&&(b&&c) := by
  cases a <;> cases b <;> cases c <;> rfl
/-- Pure Boolean concatenation; explicit equality composition avoids propext. -/
theorem append (check : Nat→Bool) (n m : Nat) :
    ∀i, allFrom check i (n+m)=(allFrom check i n &&allFrom check (i+n) m) := by
  induction n with
  | zero =>
    intro i
    rw [Nat.zero_add,Nat.add_zero]
    rfl
  | succ n ih =>
    intro i
    rw [Nat.succ_add]
    change (check i && allFrom check (i+1) (n+m)) =
      ((check i && allFrom check (i+1) n) && allFrom check (i+(n+1)) m)
    have address : (i+1)+n=i+(n+1) :=
      (Nat.add_assoc i 1 n).trans (congrArg (Nat.add i) (Nat.add_comm 1 n))
    exact (congrArg (fun b => check i && b) (ih (i+1))).trans
      ((and_assoc_pure (check i) (allFrom check (i+1) n)
        (allFrom check ((i+1)+n) m)).symm.trans
          (congrArg (fun b => (check i && allFrom check (i+1) n) && b)
            (congrArg (fun j => allFrom check j m) address)))
theorem append_checked {check : Nat→Bool} {i n m : Nat}
    (left : allFrom check i n=true) (right : allFrom check (i+n) m=true) :
    allFrom check i (n+m)=true := by
  have h:=append check n m i
  rw [left,right] at h
  exact h
#print axioms append
#print axioms append_checked
end RamanujanPV.HighCheck0006SplitPilot
