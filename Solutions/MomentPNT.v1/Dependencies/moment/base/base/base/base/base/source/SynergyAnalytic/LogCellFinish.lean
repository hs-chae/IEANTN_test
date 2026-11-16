import SynergyAnalytic.VectorExpr
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def finishLog (h s : ProofBox) : Option ProofBox := do
  if 0 < s.lo then
    let v ← BoxModel.logPos 384 (inv p s)
    pure (add h (mul p (literal p 6 1) v))
  else none

theorem finishLog_sound {h s out : ProofBox} {x y : ℝ}
    (hh : RealBox.Contains p h x) (hs : RealBox.Contains p s y)
    (hr : finishLog h s=some out) :
    RealBox.Contains p out (x+6*Real.log y⁻¹) := by
  unfold finishLog at hr
  by_cases hlo : 0 < s.lo
  · simp only [hlo,ite_true] at hr
    cases he:BoxModel.logPos 384 (inv p s) with
    | none => simp [he] at hr
    | some v =>
      simp only [he,Bind.bind,Option.bind,Option.pure_def,Option.some.injEq] at hr
      subst out
      have hinv := RealBox.inv_sound hs (Or.inl hlo)
      have hlog := BoxModel.logPos_sound 384 hinv he
      have h6 : RealBox.Contains p (literal p 6 1) (6:ℝ) := by
        simpa only [Int.cast_ofNat,Nat.cast_one,div_one] using RealBox.literal_sound p 6 1 (by decide)
      exact RealBox.add_sound hh (RealBox.mul_sound h6 hlog)
  · simp [hlo] at hr

#print axioms finishLog_sound
end SynergyAnalytic.HeightPoint
