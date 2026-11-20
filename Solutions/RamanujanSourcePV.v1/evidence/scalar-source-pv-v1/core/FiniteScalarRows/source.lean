import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
namespace RamanujanPV.FiniteScalarRows
set_option autoImplicit false
set_option Elab.async false
/-- An exact consecutive proof population. Each original row contributes one
proof, and extraction preserves its absolute original index. -/
inductive RangeProof (property : Nat→Prop) : Nat→Nat→Prop
  | nil (start : Nat) : RangeProof property start 0
  | cons {start count : Nat} : property start →RangeProof property (start+1) count →
      RangeProof property start (count+1)

theorem RangeProof.at {property : Nat→Prop} {start count i : Nat}
    (proof : RangeProof property start count) (lower : start ≤ i) (upper : i < start+count) : property i := by
  induction proof with
  | nil start=>omega
  | @cons start count first rest ih=>
    by_cases eq:i=start
    · subst i;exact first
    · exact ih (by omega) (by omega)

theorem RangeProof.append {property : Nat→Prop} {start a b : Nat}
    (left:RangeProof property start a) (right:RangeProof property (start+a) b) :
    RangeProof property start (a+b) := by
  induction left with
  | nil start=>simpa using right
  | @cons start count first rest ih=>
    have later : RangeProof property ((start+1)+count) b := by
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using right
    have tail:=ih later
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using RangeProof.cons first tail
#print axioms RangeProof.at
#print axioms RangeProof.append
end RamanujanPV.FiniteScalarRows
