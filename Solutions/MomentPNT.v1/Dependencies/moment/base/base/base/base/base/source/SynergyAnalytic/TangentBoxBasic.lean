import SynergyAnalytic.TangentCompute
import SynergyAnalytic.TangentMoments
namespace SynergyAnalytic.BoxModel
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0

 theorem rat_sound (n d:Nat) (hd:0 < d) :
    RealBox.Contains p (rat n d) ((n:ℝ)/d) := by
  simpa only [rat,Int.cast_natCast] using RealBox.literal_sound p (n:Int) d hd

 theorem sourcePower_sound {a:ProofBox} {x:ℝ} (ha:RealBox.Contains p a x) (n:Nat) :
    RealBox.Contains p (sourcePower a n) (x^n) := by
  induction n with
  | zero => simpa only [sourcePower,pow_zero] using one_sound
  | succ n ih => simpa only [sourcePower,pow_succ] using RealBox.mul_sound ih ha

 theorem safeDiv_sound {a b out:ProofBox} {x y:ℝ}
    (ha:RealBox.Contains p a x) (hb:RealBox.Contains p b y) (hx:0 ≤ x)
    (hr:safeDiv a b=some out) : RealBox.Contains p out (x/y) := by
  unfold safeDiv at hr
  by_cases hg:0 < b.lo
  · simp only [if_pos hg,Option.some.injEq] at hr
    subst out
    exact divI_sound ha hb hx hg
  · simp [hg] at hr

 theorem safeExp_sound {a out:ProofBox} {x:ℝ}
    (ha:RealBox.Contains p a x) (hr:safeExp a=some out) :
    RealBox.Contains p out (Real.exp (-x)) := by
  unfold safeExp at hr
  by_cases hg:a.lo < 0 ∨ a.hi < a.lo ∨ 64*scale p < a.hi
  · simp [hg] at hr
  · simp only [if_neg hg,Option.some.injEq] at hr
    subst out
    have hp:=RealBox.scale_real_pos p
    have hlo : (0:ℝ) ≤ (a.lo:ℝ) := by exact_mod_cast le_of_not_gt (not_or.mp hg).1
    have hhi : (a.hi:ℝ) ≤ 64*(scale p:ℝ) := by
      exact_mod_cast le_of_not_gt (not_or.mp (not_or.mp hg).2).2
    apply expNeg_sound ha
    · nlinarith [ha.1]
    · nlinarith [ha.2]

 theorem newtonStep_sound {left a out:ProofBox} {x u:ℝ}
    (hl:RealBox.Contains p left x) (ha:RealBox.Contains p a u) (hx:0 ≤ x)
    (hr:newtonStep left a=some out) :
    RealBox.Contains p out (SynergyAnalytic.tangentUpdate x u) := by
  unfold newtonStep at hr
  cases hq:safeDiv left (mul p a a) with
  | none => simp [hq] at hr
  | some quotient =>
    simp only [hq,Option.bind_eq_bind,Option.bind_some,Option.pure_def,Option.some.injEq] at hr
    subst out
    have ht:=rat_sound 2 1 (by decide)
    norm_num only [Nat.cast_ofNat,div_one] at ht
    have hh:=divN_sound (RealBox.add_sound (RealBox.mul_sound ht ha)
      (safeDiv_sound hl (RealBox.mul_sound ha ha) hx hq)) (by decide : 0<(3:Nat))
    simpa only [SynergyAnalytic.tangentUpdate,pow_two,Nat.cast_ofNat] using hh

 theorem newtonParameter_sound {left out:ProofBox} {x:ℝ}
    (hl:RealBox.Contains p left x) (hx:0 < x) (hr:newtonParameter left=some out) :
    RealBox.Contains p out (SynergyAnalytic.tangentNewton2 x) := by
  have ht:=rat_sound 2 1 (by decide)
  norm_num only [Nat.cast_ofNat,div_one] at ht
  have hs:=divN_sound (RealBox.add_sound hl ht) (by decide : 0<(3:Nat))
  change RealBox.Contains p (divN (add left (rat 2 1)) 3) (SynergyAnalytic.tangentSeed x) at hs
  unfold newtonParameter at hr
  cases hb:newtonStep left (divN (add left (rat 2 1)) 3) with
  | none => simp [hb] at hr
  | some b =>
    simp only [hb,Option.bind_eq_bind,Option.bind_some] at hr
    have hfirst:=newtonStep_sound hl hs hx.le hb
    have hlast:=newtonStep_sound hl hfirst hx.le hr
    exact hlast

#print axioms newtonParameter_sound
#print axioms safeExp_sound
end SynergyAnalytic.BoxModel
