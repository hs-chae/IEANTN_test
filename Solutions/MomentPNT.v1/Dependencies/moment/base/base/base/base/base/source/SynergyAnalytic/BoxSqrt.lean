import SynergyBasis.PositiveDivision
import Mathlib.Data.Nat.Sqrt
namespace SynergyAnalytic.BoxModel
open ScopedNumerical ScopedNumerical.ProofBox
open SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Directed square-root model on the same128-bit grid. The source's integer
binary search must separately be connected to these floor square roots. -/
def sqrtBox (a : ProofBox) : ProofBox :=
  ⟨(Nat.sqrt (a.lo.toNat*(scale p).toNat) : Int),
   (Nat.sqrt (a.hi.toNat*(scale p).toNat) : Int)+1⟩

theorem sqrtBox_sound {a : ProofBox} {x : ℝ}
    (ha : RealBox.Contains p a x) (ha0 : 0 ≤ a.lo) :
    RealBox.Contains p (sqrtBox a) (Real.sqrt x) := by
  have hp := RealBox.scale_real_pos p
  have hpi : 0 ≤ scale p := (RealBox.scale_pos p).le
  have hlo : (0:ℝ) ≤ (a.lo:ℝ) := by exact_mod_cast ha0
  have hx : 0 ≤ x := by nlinarith [ha.1]
  have hhi : 0 ≤ a.hi := by
    have hh : (0:ℝ) ≤ (a.hi:ℝ) := (mul_nonneg hx hp.le).trans ha.2
    exact_mod_cast hh
  have hsqrt0 := Real.sqrt_nonneg x
  have hsqrt2 := Real.sq_sqrt hx
  have hl := Nat.sqrt_le' (a.lo.toNat*(scale p).toNat)
  have hh := (Nat.lt_succ_sqrt' (a.hi.toNat*(scale p).toNat)).le
  have hloNat : (a.lo.toNat:ℝ) = (a.lo:ℝ) := by exact_mod_cast Int.toNat_of_nonneg ha0
  have hhiNat : (a.hi.toNat:ℝ) = (a.hi:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hhi
  have hscaleNat : ((scale p).toNat:ℝ) = (scale p:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hpi
  have hlR : (Nat.sqrt (a.lo.toNat*(scale p).toNat):ℝ)^2 ≤ (a.lo:ℝ)*(scale p:ℝ) := by
    have hcast : (Nat.sqrt (a.lo.toNat*(scale p).toNat):ℝ)^2 ≤ (a.lo.toNat:ℝ)*(scale p).toNat := by exact_mod_cast hl
    simpa only [hloNat,hscaleNat] using hcast
  have hhR : (a.hi:ℝ)*(scale p:ℝ) ≤ ((Nat.sqrt (a.hi.toNat*(scale p).toNat):ℝ)+1)^2 := by
    have hcast : (a.hi.toNat:ℝ)*(scale p).toNat ≤ ((Nat.sqrt (a.hi.toNat*(scale p).toNat):ℝ)+1)^2 := by exact_mod_cast hh
    simpa only [hhiNat,hscaleNat] using hcast
  have hloCast : 0 ≤ (Nat.sqrt (a.lo.toNat*(scale p).toNat):ℝ) := Nat.cast_nonneg _
  have hhiCast : 0 ≤ (Nat.sqrt (a.hi.toNat*(scale p).toNat):ℝ) := Nat.cast_nonneg _
  have hmul := mul_nonneg hsqrt0 hp.le
  have he : (Real.sqrt x*(scale p:ℝ))^2=x*(scale p:ℝ)^2 := by rw [mul_pow,hsqrt2]
  simp only [RealBox.Contains,sqrtBox,Int.cast_natCast,Int.cast_add,Int.cast_one]

  constructor
  · change (Nat.sqrt (a.lo.toNat*(scale p).toNat):ℝ) ≤ Real.sqrt x*(scale p:ℝ)
    have hbound := mul_le_mul_of_nonneg_right ha.1 hp.le
    nlinarith
  · change Real.sqrt x*(scale p:ℝ) ≤ ((Nat.sqrt (a.hi.toNat*(scale p).toNat):Int)+1:ℝ)
    push_cast
    have hbound := mul_le_mul_of_nonneg_right ha.2 hp.le
    nlinarith

#print axioms sqrtBox_sound
end SynergyAnalytic.BoxModel
