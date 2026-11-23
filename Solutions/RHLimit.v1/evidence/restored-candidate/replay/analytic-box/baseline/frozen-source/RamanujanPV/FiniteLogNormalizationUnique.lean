/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteLogNormalize
namespace RamanujanPV.FiniteLogNormalizationUnique
set_option autoImplicit false

/-- Two integer powers of two whose half-open binary cells contain the same
integer necessarily give the same exponent and normalization value. -/
theorem unique {n two two' k k' : Nat}
    (hp : two=2^k) (low : two≤n) (high : n<2*two)
    (hp' : two'=2^k') (low' : two'≤n) (high' : n<2*two') :
    two=two' ∧ k=k' := by
  have left : ¬k<k' := by
    intro less
    have h:=Nat.pow_le_pow_right (n:=2) (by decide : 0<2) (i:=k+1) (j:=k') (by omega)
    rw [pow_succ,←hp,←hp'] at h
    omega
  have right : ¬k'<k := by
    intro less
    have h:=Nat.pow_le_pow_right (n:=2) (by decide : 0<2) (i:=k'+1) (j:=k) (by omega)
    rw [pow_succ,←hp',←hp] at h
    omega
  have eq : k=k' := by omega
  exact ⟨by rw [hp,hp',eq],eq⟩

#print axioms unique
end RamanujanPV.FiniteLogNormalizationUnique
