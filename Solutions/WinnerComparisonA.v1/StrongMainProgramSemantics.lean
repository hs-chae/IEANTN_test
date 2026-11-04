/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongDataSemantics
import StrongMain0
import StrongMain1
import StrongMain2
namespace WinnerStrongOuter
open LeanCert.Core LeanCert.Engine Real WinnerOldFloors WinnerOldOuter.Assembly WinnerOldOuter.Arbitrary
set_option maxHeartbeats 0
 theorem bounds_at_grid (v0 step : ℚ) (k : ℕ) (hv : 0≤v0) (hs : 0≤step) :
    evalData (bounds (add (lit v0) (mul (lit step) (.var 0)))
      (add (add (lit v0) (mul (lit step) (.var 0))) (lit step))) (sumBodyRealEnv k)=
      WinnerStrongEnvelope.data v0 step k := by
  let vl:=add (lit v0) (mul (lit step) (.var 0))
  let vr:=add vl (lit step)
  have hevl : Expr.eval (sumBodyRealEnv k) vl=(v0:ℝ)+(step:ℝ)*k := by rfl
  have hevr : Expr.eval (sumBodyRealEnv k) vr=(v0:ℝ)+(step:ℝ)*k+step := by rfl
  have hvR : (0:ℝ)≤v0 := by exact_mod_cast hv
  have hsR : (0:ℝ)≤step := by exact_mod_cast hs
  have hp : 0<WinnerOldFloors.h+Expr.eval (sumBodyRealEnv k) vr := by
    rw [hevr]
    have hh:=h_lower
    positivity
  have hb:=boundsData_semantics vl vr (sumBodyRealEnv k) hp
  rw [hevl,hevr,add_sub_cancel_left,data_row_between] at hb
  exact hb
 theorem mass_semantics (e : Expr) (width : ℚ) (env : ℕ→ℝ) :
    Expr.eval env (mass e width)=WinnerOldAnalytic.expMass (Expr.eval env e) width := by
  simp only [mass,WinnerOldAnalytic.expMass,eval_div,eval_sub,eval_lit,eval_exp,eval_mul,eval_neg]
  norm_num only [Rat.cast_ofNat]
  rw [neg_mul]
 theorem main_body_semantics (v0 step width : ℚ) (k : ℕ) (hv : 0≤v0) (hs : 0≤step) :
    Expr.eval (sumBodyRealEnv k) (mainBody v0 step width)=
      600*(step:ℝ)*closedMass (30001/100) width ((3663/5000)*Real.pi)
        (WinnerStrongEnvelope.data v0 step k) := by
  let vl:=add (lit v0) (mul (lit step) (.var 0))
  let vr:=add vl (lit step)
  let c:=bounds vl vr
  let d:=WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k
  have hb:evalData c (sumBodyRealEnv k)=d := bounds_at_grid v0 step k hv hs
  have hul:=congrArg CellData.ul hb
  have hur:=congrArg CellData.ur hb
  have hzl:=congrArg CellData.zl hb
  have hzu:=congrArg CellData.zu hb
  have hbl:=congrArg CellData.Bl hb
  have hbu:=congrArg CellData.Bu hb
  have hr:=congrArg CellData.rmin hb
  change Expr.eval (sumBodyRealEnv k)
    (mul (dv (lit (600*step)) (mul (lit (3663/5000)) (.namedConst .pi)))
      (sub (mul c.ul (mul c.zl (mass (sub (lit (30001/100)) c.bl) width)))
        (mul c.ur (mul (dv (sq c.zu) (mul (lit 2) c.rmin))
          (mass (sub (lit (30001/100)) (mul (lit 2) c.bu)) width)))))=_
  simp only [eval_mul,eval_div,eval_lit,eval_pi,eval_sub,eval_sq,mass_semantics]
  change Expr.eval (sumBodyRealEnv k) c.ul=d.ul at hul
  change Expr.eval (sumBodyRealEnv k) c.ur=d.ur at hur
  change Expr.eval (sumBodyRealEnv k) c.zl=d.zl at hzl
  change Expr.eval (sumBodyRealEnv k) c.zu=d.zu at hzu
  change Expr.eval (sumBodyRealEnv k) c.bl=d.Bl at hbl
  change Expr.eval (sumBodyRealEnv k) c.bu=d.Bu at hbu
  change Expr.eval (sumBodyRealEnv k) c.rmin=d.rmin at hr
  rw [hul,hur,hzl,hzu,hbl,hbu,hr]
  norm_num only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat]
  unfold closedMass
  ring
 theorem cap_body_semantics (v0 step width : ℚ) (k : ℕ) (hv : 0≤v0) (hs : 0≤step) :
    Expr.eval (sumBodyRealEnv k) (capBody v0 step width)=
      (WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k).ul*
      (WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k).zl*
        exp ((WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k).Bl*(width:ℝ))/((3663/5000)*Real.pi)-
      WinnerOldC4Source.windowMain ((v0:ℝ)+(step:ℝ)*k) := by
  let vl:=add (lit v0) (mul (lit step) (.var 0))
  let vr:=add vl (lit step)
  let c:=bounds vl vr
  let d:=WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k
  have hb:evalData c (sumBodyRealEnv k)=d := bounds_at_grid v0 step k hv hs
  have hul:=congrArg CellData.ul hb
  have hzl:=congrArg CellData.zl hb
  have hbl:=congrArg CellData.Bl hb
  have hw:=bounds_window_semantics vl vr (sumBodyRealEnv k)
  change Expr.eval (sumBodyRealEnv k) c.ul=d.ul at hul
  change Expr.eval (sumBodyRealEnv k) c.zl=d.zl at hzl
  change Expr.eval (sumBodyRealEnv k) c.bl=d.Bl at hbl
  change Expr.eval (sumBodyRealEnv k) (sub (dv (mul c.ul (mul c.zl (.exp (mul c.bl (lit width)))))
    (mul (lit (3663/5000)) (.namedConst .pi))) c.window)=_
  simp only [eval_sub,eval_div,eval_mul,eval_exp,eval_lit,eval_pi]
  rw [hul,hzl,hbl,hw]
  simp only [vl,eval_add,eval_mul,eval_lit,Expr.eval,sumBodyRealEnv]
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  ring
 theorem checkCap_sound {v0 step width : ℚ} {n k : ℕ}
    (hv : 0≤v0) (hs : 0≤step) (hk : k<n) (hc : checkCap v0 step width n=true) :
      (WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k).ul*
      (WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k).zl*
        exp ((WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k).Bl*(width:ℝ))/((3663/5000)*Real.pi)≤
      WinnerOldC4Source.windowMain ((v0:ℝ)+(step:ℝ)*k) := by
  have hh:=List.all_eq_true.mp hc k (List.mem_range.mpr hk)
  have hp:=CH2QRH.DensityComputation.verify_upper _ k k 0 cfg (by decide) hh
  simp only [Finset.Icc_self,Finset.sum_singleton,Rat.cast_zero] at hp
  rw [cap_body_semantics _ _ _ _ hv hs] at hp
  linarith
 theorem Icc_eq_range {n : ℕ} (hn : 0<n) : Finset.Icc 0 (n-1)=Finset.range n := by
  ext k
  simp only [Finset.mem_Icc,Finset.mem_range]
  omega
 theorem checkMain_sound {v0 step width target : ℚ} {n : ℕ}
    (hv : 0≤v0) (hs : 0≤step) (hn : 0<n) (hc : checkMain v0 step width target n=true) :
    (target:ℝ)≤∑k∈Finset.range n,600*(step:ℝ)*closedMass (30001/100) width ((3663/5000)*Real.pi)
      (WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k) := by
  have hh:=CH2QRH.DensityComputation.verify_upper _ 0 (n-1) (-target) cfg (by decide) hc
  simp only [Expr.eval,Finset.sum_neg_distrib,Rat.cast_neg] at hh
  rw [Icc_eq_range hn] at hh
  have hp : (target:ℝ)≤∑k∈Finset.range n,Expr.eval (sumBodyRealEnv k) (mainBody v0 step width) := by linarith
  simpa only [main_body_semantics _ _ _ _ hv hs] using hp
#print axioms main_body_semantics
#print axioms checkMain_sound
#print axioms checkCap_sound
end WinnerStrongOuter
