import RamanujanPV.QuotientDemandCheck

/-! Proof-evaluation control for the unchanged large numerical count certificate.
This is a Lean-native certificate checker, explicitly NOT source-first PV. Its
general correctness theorem transports the result to the original exact
allFrom/checkEntry proposition, with no alteration to records or C counter. -/
namespace RHOcticPush.BalancedCount
open RamanujanPV.QuotientDemandCheck
set_option autoImplicit false

def tree (check : Nat → Bool) : Nat → Nat → Bool
  | i,0 => check i
  | i,d+1 => tree check i d && tree check (i+2^d) d

/-- Constructive concatenation: keep numerical transport axiom-free rather
than importing the simplifier-based historical append proof. -/
theorem append_pure (check : Nat → Bool) (n m : Nat) :
    ∀ i, allFrom check i (n+m)=
      (allFrom check i n &&allFrom check (i+n) m) := by
  induction n with
  | zero =>
    intro i
    rw [Nat.zero_add]
    rfl
  | succ n ih =>
    intro i
    rw [Nat.succ_add]
    change (check i &&allFrom check (i+1) (n+m)) =
      ((check i &&allFrom check (i+1) n) &&allFrom check (i+(n+1)) m)
    rw [ih]
    have hidx : i+1+n=i+(n+1) := by rw [Nat.add_assoc,Nat.add_comm 1 n]
    rw [hidx]
    exact (Bool.and_assoc _ _ _).symm

theorem tree_eq (check : Nat → Bool) (depth : Nat) :
    ∀ i, tree check i depth=allFrom check i (2^depth) := by
  induction depth with
  | zero =>
    intro i
    change check i=(check i &&true)
    exact (Bool.and_true _).symm
  | succ depth ih =>
    intro i
    have hp : (2:Nat)^(depth+1)=2^depth+2^depth := by rw [pow_succ,Nat.mul_two]
    calc tree check i (depth+1)
        = (tree check i depth &&tree check (i+2^depth) depth) := rfl
      _ = (allFrom check i (2^depth) &&allFrom check (i+2^depth) (2^depth)) :=
        congrArg₂ Bool.and (ih i) (ih (i+2^depth))
      _ = allFrom check i (2^depth+2^depth) := (append_pure check _ _ i).symm
      _ = allFrom check i (2^(depth+1)) := congrArg (allFrom check i) hp.symm

theorem tree_sound {check : Nat → Bool} {i depth : Nat}
    (checked : tree check i depth=true) : allFrom check i (2^depth)=true := by
  exact (tree_eq check depth i).symm.trans checked

/-- A literal-length export prevents the concrete kernel goal from unfolding
the huge linear checker just to compare a power expression with its numeral. -/
theorem source_32768 {check : Nat → Bool} {i : Nat}
    (checked : tree check i 15=true) : allFrom check i 32768=true := by
  exact tree_sound checked

#print axioms append_pure
#print axioms tree_eq
#print axioms tree_sound
#print axioms source_32768
end RHOcticPush.BalancedCount
