import SynergyBasis.PositiveLog
import SynergyBasis.PositiveDivision
namespace SynergyAnalytic.BoxModel
open ScopedNumerical ScopedNumerical.ProofBox
open SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- Same halving order as the actual source while loop; fuel is only a
termination instrument. Accepted calls must stop before it is exhausted. -/
def reduceLog : Nat→ProofBox→Option (ProofBox×Nat)
  | 0,m=>if 2*scale p < m.lo then none else some (m,0)
  | fuel+1,m=>if 2*scale p < m.lo then do
      let r←reduceLog fuel (divN m 2)
      pure (r.1,r.2+1)
    else some (m,0)

def logPos (fuel:Nat) (x:ProofBox) : Option ProofBox := do
  if x.lo < scale p ∨ x.hi < x.lo then none else do
    let (m,k)←reduceLog fuel x
    if 3*scale p < m.hi then none else do
      let r:=divI (positiveSub m one) (add m one)
      if r.hi < r.lo ∨ scale p < 2*r.hi then none else
        pure (add (atanh2 r) (mul p (literal p k 1) (atanh2 (literal p 1 3))))

 theorem lower_scale_real {a:ProofBox} {x:ℝ}
    (ha:RealBox.Contains p a x) (hlo:scale p ≤ a.lo) : 1 ≤ x := by
  have hp:=RealBox.scale_real_pos p
  have hh : (scale p:ℝ) ≤ (a.lo:ℝ) := by exact_mod_cast hlo
  nlinarith [ha.1]

 theorem half_lower {a:ProofBox} (ha:2*scale p < a.lo) :
    scale p ≤ (divN a 2).lo := by
  change scale p ≤ floorDiv a.lo (2:Int)
  simp only [floorDiv,show (0:Int)<2 by decide,ite_true]
  omega

 theorem reduceLog_sound (fuel:Nat) {a b:ProofBox} {x:ℝ} {k:Nat}
    (ha:RealBox.Contains p a x) (hlo:scale p ≤ a.lo)
    (hr:reduceLog fuel a=some (b,k)) :
    RealBox.Contains p b (x/(2:ℝ)^k) ∧ scale p ≤ b.lo ∧ b.lo ≤ 2*scale p := by
  induction fuel generalizing a b x k with
  | zero =>
    by_cases hc:2*scale p < a.lo
    · simp [reduceLog,hc] at hr
    · simp only [reduceLog,hc,ite_false,Option.some.injEq,Prod.mk.injEq] at hr
      rcases hr with ⟨rfl,rfl⟩
      simpa only [pow_zero,div_one] using And.intro ha (And.intro hlo (le_of_not_gt hc))
  | succ fuel ih =>
    by_cases hc:2*scale p < a.lo
    · cases hm:reduceLog fuel (divN a 2) with
      | none => simp [reduceLog,hc,hm] at hr
      | some pair =>
        rcases pair with ⟨b',k'⟩
        simp only [reduceLog,hc,ite_true,hm,Option.bind_some,Option.pure_def,
          Option.some.injEq,Prod.mk.injEq] at hr
        rcases hr with ⟨rfl,rfl⟩
        have hh:=ih (divN_sound ha (by norm_num : 0<(2:Nat))) (half_lower hc) hm
        have he : x/2/(2:ℝ)^k'=x/(2:ℝ)^(k'+1) := by rw [pow_succ];ring
        simpa only [Nat.cast_ofNat,he] using hh
    · simp only [reduceLog,hc,ite_false,Option.some.injEq,Prod.mk.injEq] at hr
      rcases hr with ⟨rfl,rfl⟩
      simpa only [pow_zero,div_one] using And.intro ha (And.intro hlo (le_of_not_gt hc))

 theorem reduced_ratio_sound {m:ProofBox} {y:ℝ}
    (hm:RealBox.Contains p m y) (hlo:scale p ≤ m.lo) (hhi:m.hi ≤ 3*scale p) :
    RealBox.Contains p (divI (positiveSub m one) (add m one)) ((y-1)/(y+1)) ∧
      0 ≤ (y-1)/(y+1) ∧ (y-1)/(y+1) ≤ 1/2 := by
  have hy:=lower_scale_real hm hlo
  have hp:=RealBox.scale_real_pos p
  have hhiR : (m.hi:ℝ) ≤ 3*(scale p:ℝ) := by exact_mod_cast hhi
  have hy3 : y ≤ 3 := by nlinarith [hm.2]
  have hsub:=positiveSub_sound hm one_sound
  rw [max_eq_right (by linarith : 0 ≤ y-1)] at hsub
  have hadd:=RealBox.add_sound hm one_sound
  have hs : 0 < scale p := by norm_num [scale,p]
  have hden : 0 < (add m one).lo := by change 0 < m.lo+scale p;omega
  refine ⟨divI_sound hsub hadd (by linarith) hden,by positivity,?_⟩
  apply (div_le_iff₀ (by linarith : 0 < y+1)).mpr
  linarith

 theorem ratio_log {y:ℝ} (hy:1 ≤ y) :
    Real.log ((1+(y-1)/(y+1))/(1-(y-1)/(y+1)))=Real.log y := by
  congr 1
  have hy1 : y+1 ≠ 0 := by linarith
  field_simp
  <;> ring

 theorem logPos_sound (fuel:Nat) {a out:ProofBox} {x:ℝ}
    (ha:RealBox.Contains p a x) (hr:logPos fuel a=some out) :
    RealBox.Contains p out (Real.log x) := by
  unfold logPos at hr
  by_cases hbad:a.lo < scale p ∨ a.hi < a.lo
  · simp only [if_pos hbad] at hr
    contradiction
  · simp only [if_neg hbad] at hr
    have hlo : scale p ≤ a.lo := le_of_not_gt (not_or.mp hbad).1
    cases hm:reduceLog fuel a with
    | none => simp [hm] at hr
    | some pair =>
      rcases pair with ⟨m,k⟩
      simp only [hm,Option.bind_eq_bind,Option.bind_some] at hr
      try dsimp only at hr
      by_cases hhi:3*scale p < m.hi
      · simp only [if_pos hhi] at hr
        contradiction
      · simp only [if_neg hhi] at hr
        try dsimp only at hr
        by_cases hratio:(divI (positiveSub m one) (add m one)).hi <
            (divI (positiveSub m one) (add m one)).lo ∨
            scale p < 2*(divI (positiveSub m one) (add m one)).hi
        · simp only [if_pos hratio] at hr
          contradiction
        · simp only [if_neg hratio,Option.pure_def,Option.some.injEq] at hr
          subst out
          have hreduce:=reduceLog_sound fuel ha hlo hm
          have hratioSound:=reduced_ratio_sound hreduce.1 hreduce.2.1 (le_of_not_gt hhi)
          have hy:=lower_scale_real hreduce.1 hreduce.2.1
          have hh:=atanh2_sound hratioSound.1 hratioSound.2.1 hratioSound.2.2
          rw [ratio_log hy] at hh
          have hk : RealBox.Contains p (literal p k 1) (k:ℝ) := by
            simpa using RealBox.literal_sound p (k:Int) 1 (by decide)
          have hs:=RealBox.add_sound hh (RealBox.mul_sound hk ln2_sound)
          have hx : 0 < x := by have hh:=lower_scale_real ha hlo;linarith
          have he : Real.log (x/(2:ℝ)^k)+(k:ℝ)*Real.log 2=Real.log x := by
            rw [Real.log_div hx.ne' (pow_ne_zero k (by norm_num)),Real.log_pow]
            ring
          rw [he] at hs
          exact hs

#print axioms reduceLog_sound
#print axioms logPos_sound
end SynergyAnalytic.BoxModel
