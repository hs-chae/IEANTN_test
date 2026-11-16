import SynergyAnalytic.TangentCompute
namespace SynergyAnalytic.BoxModel
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0

theorem sourceDot_sound {coeff moments:Fin 5→ProofBox} {C M:Nat→ℝ}
    (hc:∀k:Fin 5,RealBox.Contains p (coeff k) (C k.val))
    (hm:∀k:Fin 5,RealBox.Contains p (moments k) (M k.val))
    (n:Nat) (hn:n ≤ 5) :
    RealBox.Contains p (sourceDot coeff moments n) (∑k∈Finset.range n,C k*M k) := by
  induction n with
  | zero => simpa only [sourceDot,Finset.sum_range_zero] using zero_sound
  | succ n ih =>
    have hk:n < 5 := by omega
    have hh:=RealBox.add_sound (ih (by omega)) (RealBox.mul_sound (hc ⟨n,hk⟩) (hm ⟨n,hk⟩))
    simpa only [sourceDot,dif_pos hk,Finset.sum_range_succ] using hh

#print axioms sourceDot_sound
end SynergyAnalytic.BoxModel
