/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteLogBounds

namespace RamanujanPV.FiniteLogBounds
set_option autoImplicit false

theorem normalization_k_bound {n two k : Nat} (hpow : two=2^k)
    (low : two≤n) (upper : n≤2000000000000) : k≤40 := by
  by_contra bad
  have large := Nat.pow_le_pow_right (n:=2) (by decide : 0<2) (i:=41) (j:=k) (by omega)
  rw [←hpow] at large
  norm_num at large
  omega

theorem normalization_step {n two k : Nat} (hpow : two=2^k)
    (upper : n≤2000000000000) (guard : two≤n/2) :
    two*2=2^(k+1) ∧ two*2≤n ∧ k+1≤40 ∧ two*2<2^64 ∧ k+1<2^64 := by
  have nextPow : two*2=2^(k+1) := by rw [hpow,pow_succ]
  have nextLow : two*2≤n := (Nat.le_div_iff_mul_le (by decide : 0<2)).mp guard
  have kNext := normalization_k_bound nextPow nextLow upper
  exact ⟨nextPow,nextLow,kNext,by norm_num at upper ⊢; omega,by norm_num at kNext ⊢; omega⟩

theorem normalization_stop {n two k : Nat} (hpow : two=2^k)
    (low : two≤n) (upper : n≤2000000000000) (stop : ¬two≤n/2) :
    0<two ∧ two≤n ∧ n<2*two ∧ k≤40 := by
  refine ⟨by rw [hpow]; positivity,low,?_,normalization_k_bound hpow low upper⟩
  omega

theorem normalized_public_bound {n two k : Nat} (hpow : two=2^k)
    (low : two≤n) (upper : n≤2000000000000) (stop : ¬two≤n/2) :
    AnalyticTransition.binaryLogUpper n two k < 2^64 := by
  have facts := normalization_stop hpow low upper stop
  exact binary_output_u64 low facts.2.2.1 facts.2.2.2

#print axioms normalization_k_bound
#print axioms normalization_step
#print axioms normalized_public_bound
end RamanujanPV.FiniteLogBounds
