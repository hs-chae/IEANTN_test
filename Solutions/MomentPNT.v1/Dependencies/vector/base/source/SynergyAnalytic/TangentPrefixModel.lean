import SynergyAnalytic.TangentMomentModel
import SynergyAnalytic.TangentCoefficientModel
import SynergyAnalytic.TangentDotModel
namespace SynergyAnalytic.BoxModel
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Functional interval soundness for all three returned cell bounds.
C-source execution/word safety is intentionally a distinct theorem layer. -/
theorem sourceCell_prefix_sound {left width:ProofBox} {x w:ℝ}
    {out:ProofBox×ProofBox×ProofBox}
    (hl:RealBox.Contains p left x) (hw:RealBox.Contains p width w)
    (hx:0 < x) (hwp:0 ≤ w) (hr:sourceCell left width false=some out) :
    RealBox.Contains p out.1 (SynergyAnalytic.tangentUpper x (SynergyAnalytic.tangentNewton2 x) w 0) := by
  simp [sourceCell,Option.bind_eq_some_iff] at hr
  rcases hr with ⟨a,hparam,coeff,hcoeff,common,hcommon,m0,hm0,m1,hm1,m2,hm2,
    m3,hm3,m4,hm4,gaussian,hgaussian,invLeft,_hinv,hout⟩
  try subst out
  let rate:ℝ:=2*(601/2500:ℝ)*x
  have h2:=rat_sound 2 1 (by decide)
  have hq:=rat_sound 601 2500 (by decide)
  norm_num only [Nat.cast_ofNat,div_one] at h2 hq
  have hlambda : RealBox.Contains p (mul p (rat 2 1) (mul p (rat 601 2500) left)) rate := by
    convert RealBox.mul_sound h2 (RealBox.mul_sound hq hl) using 1 <;> first | rfl | (dsimp [rate];ring)
  have hrp : 0 < rate := by dsimp [rate];positivity
  have he:=safeExp_sound (RealBox.mul_sound hlambda hw) hcommon
  simp only [←neg_mul] at he
  have hM0:=sourceMoment_sound 0 hlambda hw he hrp hwp hm0
  have hM1:=sourceMoment_sound 1 hlambda hw he hrp hwp hm1
  have hM2:=sourceMoment_sound 2 hlambda hw he hrp hwp hm2
  have hM3:=sourceMoment_sound 3 hlambda hw he hrp hwp hm3
  have hM4:=sourceMoment_sound 4 hlambda hw he hrp hwp hm4
  let moments:Fin 5→ProofBox:=fun k=>if k.val=0 then m0 else if k.val=1 then m1
    else if k.val=2 then m2 else if k.val=3 then m3 else m4
  have hM : ∀k:Fin 5,RealBox.Contains p (moments k) (SynergyAnalytic.exponentialMoment k.val rate w) := by
    intro k
    fin_cases k
    · exact hM0
    · exact hM1
    · exact hM2
    · exact hM3
    · exact hM4
  have hA:=newtonParameter_sound hl hx hparam
  have hC0:=sourceCoefficients_sound hl hA hcoeff
  change ∀k:Fin 5,RealBox.Contains p (coeff k)
    (SynergyAnalytic.tangentCoefficient x (SynergyAnalytic.tangentNewton2 x) 0 k.val) at hC0
  have hG:=safeExp_sound (RealBox.mul_sound hq (RealBox.mul_sound hl hl)) hgaussian
  simp only [←neg_mul,←pow_two] at hG
  have hD0:=sourceDot_sound (C:=SynergyAnalytic.tangentCoefficient x (SynergyAnalytic.tangentNewton2 x) 0)
    (M:=fun k=>SynergyAnalytic.exponentialMoment k rate w) (moments:=moments) hC0 hM 5 (by decide)
  simpa [SynergyAnalytic.tangentUpper,rate,moments] using RealBox.mul_sound hG hD0

#print axioms sourceCell_prefix_sound
end SynergyAnalytic.BoxModel
