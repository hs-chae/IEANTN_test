import SynergyAnalytic.TangentBoxBasic
namespace SynergyAnalytic.BoxModel
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0

 theorem sourceCoefficients_sound {left a:ProofBox} {x u:ℝ} {coeff:Fin 5→ProofBox}
    (hl:RealBox.Contains p left x) (ha:RealBox.Contains p a u)
    (hr:sourceCoefficients left a=some coeff) :
    ∀k:Fin 5,RealBox.Contains p (coeff k) (SynergyAnalytic.rootCoefficient x u k.val) := by
  unfold sourceCoefficients at hr
  cases hb:safeDiv one (mul p (rat 6 1) (sourcePower a 5)) with
  | none => simp [hb] at hr
  | some B =>
    simp only [hb,Option.bind_eq_bind,Option.bind_some,Option.pure_def,Option.some.injEq] at hr
    subst coeff
    have h5:=rat_sound 5 1 (by decide)
    have h6:=rat_sound 6 1 (by decide)
    have h2:=rat_sound 2 1 (by decide)
    norm_num only [Nat.cast_ofNat,div_one] at h5 h6 h2
    have hA:=divN_sound (RealBox.mul_sound h5 ha) (by decide : 0<(6:Nat))
    have hB:=safeDiv_sound one_sound (RealBox.mul_sound h6 (sourcePower_sound ha 5))
      (by norm_num : (0:ℝ) ≤ 1) hb
    have hzero : RealBox.Contains p (add (divN (mul p (rat 5 1) a) 6)
      (mul p B (mul p left left))) (SynergyAnalytic.rootCoefficient x u 0) := by
      convert RealBox.add_sound hA (RealBox.mul_sound hB (RealBox.mul_sound hl hl)) using 1 <;> first
        | rfl
        | (norm_num [SynergyAnalytic.rootCoefficient];ring)
    have hone : RealBox.Contains p (mul p (rat 2 1) (mul p B left))
        (SynergyAnalytic.rootCoefficient x u 1) := by
      convert RealBox.mul_sound h2 (RealBox.mul_sound hB hl) using 1 <;> first
        | rfl
        | (norm_num [SynergyAnalytic.rootCoefficient];ring)
    have htwo : RealBox.Contains p B (SynergyAnalytic.rootCoefficient x u 2) := by
      simpa [SynergyAnalytic.rootCoefficient] using hB
    intro k
    by_cases hk0:k.val=0
    · simpa only [hk0,ite_true] using hzero
    · by_cases hk1:k.val=1
      · simpa [hk0,hk1] using hone
      · by_cases hk2:k.val=2
        · simpa [hk0,hk1,hk2] using htwo
        · simpa [SynergyAnalytic.rootCoefficient,hk0,hk1,hk2] using zero_sound

 theorem convolve_sound {coeff:Fin 5→ProofBox} {C:Nat→ℝ} {logLeft invLeft:ProofBox} {left:ℝ}
    (hc:∀k:Fin 5,RealBox.Contains p (coeff k) (C k.val))
    (hl:RealBox.Contains p logLeft (Real.log left))
    (hi:RealBox.Contains p invLeft (1/left)) :
    ∀k:Fin 5,RealBox.Contains p (convolve coeff logLeft invLeft k)
      (C k.val*Real.log left+if k.val=0 then 0 else C (k.val-1)/left) := by
  intro k
  unfold convolve
  by_cases hk:k.val=0
  · simp only [hk,ite_true,add_zero]
    exact RealBox.mul_sound (by simpa only [hk] using hc k) hl
  · simp only [hk,ite_false]
    convert RealBox.add_sound (RealBox.mul_sound (hc ⟨k.val-1,by omega⟩) hi)
      (RealBox.mul_sound (hc k) hl) using 1 <;> first | rfl | ring

#print axioms sourceCoefficients_sound
#print axioms convolve_sound
end SynergyAnalytic.BoxModel
