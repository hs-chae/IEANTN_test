/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldOuter
import OldAnalytic
namespace WinnerOldOuter
open LeanCert.Core LeanCert.Engine Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def outerCellReal (v0 step U V k : ℝ) : ℝ :=
  let vl := v0+step*k
  let vr := vl+step
  let ul := log 3000000000000+vl
  let ur := log 3000000000000+vr
  let dl := log (U/V)+log ul+4*ul/3
  let dr := log (U/V)+log ur+4*ur/3
  let p := 2*(3663/10000)+2*(3599/10000)*(2*(7/8)-1)
  let al := 1/4+p/(ur+3599/5000)
  let au := 1/4+p/(ul+3599/5000)
  let zl := (499999/1000000)*exp (2371/10000+al*dl+log V+2*log ul-ur)
  let zu := (501/1000)*exp (2371/10000+au*dr+log V+2*log ur-ul)
  let bl := (2-(3599/2500)/(ur+3599/5000))*dl
  let bu := (2-(3599/2500)/(ul+3599/5000))*dr
  let rmin := 1-exp (-vl)
  (600*step)/((3663/5000)*Real.pi)*
    (ul*zl*WinnerOldAnalytic.expMass (601/2-bl) (1/40)-
      ur*zu^2/(2*rmin)*WinnerOldAnalytic.expMass (601/2-2*bu) (1/40))

 theorem outerBody_semantics (v0 step U V : ℚ) (k : ℕ) :
    Expr.eval (sumBodyRealEnv k) (outerBody v0 step U V) =
      outerCellReal v0 step U V k := by
  simp only [outerBody,Expr.eval,add,mul,dv,sub,lit,sq,mass,sumBodyRealEnv,
    LeanCert.Core.MathConst.toReal,outerCellReal,WinnerOldAnalytic.expMass]
  push_cast
  ring

noncomputable def finiteLower : ℝ :=
  (∑ k ∈ Finset.Icc (0:ℕ) (494-1), outerCellReal (13/1000) (987/494000) (1698779/1000000) (36/5) k)+
  (∑ k ∈ Finset.Icc (0:ℕ) (500-1), outerCellReal 1 (1/500) (336493/200000) (719/100) k)+
  (∑ k ∈ Finset.Icc (0:ℕ) (1000-1), outerCellReal 2 (1/500) (1652763/1000000) (179/25) k)+
  (∑ k ∈ Finset.Icc (0:ℕ) (2000-1), outerCellReal 4 (1/500) (1602809/1000000) (178/25) k)

theorem finiteLower_checked : (99234/10000000:ℝ) ≤ finiteLower := by
  have h0:=row0_lower
  have h1:=row1_lower
  have h2:=row2_lower
  have h3:=row3_lower
  simp only [row0,row1,row2,row3,outerBody_semantics] at h0 h1 h2 h3
  norm_num only [Nat.sub_self] at h0 h1 h2 h3
  unfold finiteLower
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h0 h1 h2 h3
  linarith

theorem finite_strict : (9898/1000000:ℝ) < finiteLower := by
  linarith [finiteLower_checked]
#print axioms outerBody_semantics
#print axioms finiteLower_checked
#print axioms finite_strict
end WinnerOldOuter
