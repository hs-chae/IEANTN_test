/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongMainProgramSemantics
import StrongWarmProgram
import StrongWarmCell
import WarmOuterAssembly
namespace WinnerStrongOuter
open LeanCert.Core LeanCert.Engine Real WinnerOldFloors WinnerOldOuter.Assembly WinnerOldOuter.Warm
set_option maxHeartbeats 0
 theorem softMin_semantics (a b : Expr) (env : ℕ→ℝ) :
    Expr.eval env (softMin a b)=WinnerStrongEnvelope.softMinReal (Expr.eval env a) (Expr.eval env b) := by
  have hp : 0<Expr.eval env (add (sq (sub a b)) (lit (1/1000000000000000000000000))) := by
    simp only [eval_add,eval_sq,eval_sub,eval_lit]
    norm_num only [Rat.cast_div,Rat.cast_ofNat]
    positivity
  unfold softMin
  rw [eval_div,eval_sub,eval_add,rt_semantics _ _ hp]
  simp only [eval_add,eval_sq,eval_sub,eval_lit,WinnerStrongEnvelope.softMinReal]
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
 theorem rhi_semantics (vl vr : Expr) (env : ℕ→ℝ) :
    Expr.eval env (warmRhi vl vr)=WinnerStrongEnvelope.rhiReal (Expr.eval env vl) (Expr.eval env vr) := by
  simp only [warmRhi,WinnerStrongEnvelope.rhiReal,eval_add,eval_sub,eval_lit,eval_exp,eval_neg,h_semantics]
  norm_num only [Rat.cast_ofNat]
 theorem fmax_at_grid (v0 step q : ℚ) (k : ℕ) (hv : 0 ≤ v0) (hs : 0 ≤ step) :
    Expr.eval (sumBodyRealEnv k) (warmFmax (add (lit v0) (mul (lit step) (.var 0)))
      (add (add (lit v0) (mul (lit step) (.var 0))) (lit step)) q)=
      WinnerStrongEnvelope.fmaxReal (v0:ℝ) (step:ℝ) q k := by
  let vl:=add (lit v0) (mul (lit step) (.var 0))
  let vr:=add vl (lit step)
  let c:=bounds vl vr
  let d:=WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k
  have hb:evalData c (sumBodyRealEnv k)=d := bounds_at_grid v0 step k hv hs
  have hul:=congrArg CellData.ul hb
  have hzl:=congrArg CellData.zl hb
  have hbl:=congrArg CellData.Bl hb
  have hr:=congrArg CellData.rmin hb
  change Expr.eval (sumBodyRealEnv k) c.ul=d.ul at hul
  change Expr.eval (sumBodyRealEnv k) c.zl=d.zl at hzl
  change Expr.eval (sumBodyRealEnv k) c.bl=d.Bl at hbl
  change Expr.eval (sumBodyRealEnv k) c.rmin=d.rmin at hr
  change Expr.eval (sumBodyRealEnv k) (dv (mul (mul c.ul c.rmin) (mul (lit 2) (mul c.zl (.exp (mul c.bl (lit q))))))
    (mul (mul (lit (3663/5000)) (.namedConst .pi)) (add (mul (lit 2) (warmRhi vl vr)) (mul c.zl (.exp (mul c.bl (lit q)))))))=_
  simp only [eval_div,eval_mul,eval_add,eval_lit,eval_exp,eval_pi,rhi_semantics]
  rw [hul,hzl,hbl,hr]
  simp only [vl,vr,eval_add,eval_mul,eval_lit,Expr.eval,sumBodyRealEnv]
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  rfl
 noncomputable def warmM (v0 step : ℝ) (k j : ℕ) : ℝ :=
  WinnerStrongEnvelope.softMinReal (WinnerStrongEnvelope.fmaxReal v0 step (((j:ℝ)+1)/500) k)
    (WinnerOldC4Source.windowMain (v0+step*k))
 theorem warm_term_semantics (v0 step : ℚ) (k j : ℕ) (hv : 0 ≤ v0) (hs : 0 ≤ step) :
    Expr.eval (sumBodyRealEnv k) (warmTerm v0 step j)=
      WinnerOldOuter.Warm.bandMass (30001/100) (1/500) (WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k).Bl
        (warmM v0 step k j) j := by
  let vl:=add (lit v0) (mul (lit step) (.var 0))
  let vr:=add vl (lit step)
  let c:=bounds vl vr
  let d:=WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k
  have hb:evalData c (sumBodyRealEnv k)=d := bounds_at_grid v0 step k hv hs
  have hbl:=congrArg CellData.Bl hb
  change Expr.eval (sumBodyRealEnv k) c.bl=d.Bl at hbl
  have hw:=bounds_window_semantics vl vr (sumBodyRealEnv k)
  have hf:=fmax_at_grid v0 step (((j:ℚ)+1)/500) k hv hs
  change Expr.eval (sumBodyRealEnv k) (mul (softMin (warmFmax vl vr (((j:ℚ)+1)/500)) c.window)
    (mul (.exp (.neg (mul c.bl (lit (((j:ℚ)+1)/500)))))
      (bandMass (sub (lit (30001/100)) c.bl) ((j:ℚ)/500) (((j:ℚ)+1)/500))))=_
  simp only [eval_mul,softMin_semantics,eval_exp,eval_neg,eval_sub,eval_lit,
    bandMass,eval_div]
  rw [hbl,hw,hf]
  simp only [vl,eval_add,eval_mul,eval_lit,Expr.eval,sumBodyRealEnv]
  norm_num only [Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat]
  unfold WinnerOldOuter.Warm.bandMass warmM
  dsimp only [d]
  ring_nf

 theorem eval_fold_add (f : ℕ→Expr) (ls : List ℕ) (acc : Expr) (env : ℕ→ℝ) :
    Expr.eval env (ls.foldl (fun acc j=>add acc (f j)) acc)=
      Expr.eval env acc+(ls.map (fun j=>Expr.eval env (f j))).sum := by
  induction ls generalizing acc with
  |nil=>simp
  |cons j rest ih=>
    simp only [List.foldl_cons,ih,eval_add,List.map_cons,List.sum_cons]
    ring
 theorem warm_body_semantics (v0 step : ℚ) (k : ℕ) (hv : 0 ≤ v0) (hs : 0 ≤ step) :
    Expr.eval (sumBodyRealEnv k) (warmBody v0 step)=600*(step:ℝ)*
      ∑j∈Finset.range 25,WinnerOldOuter.Warm.bandMass (30001/100) (1/500)
        (WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k).Bl (warmM v0 step k j) j := by
  unfold warmBody
  rw [eval_mul,eval_lit,eval_fold_add]
  simp only [Expr.eval,Rat.cast_zero,zero_add]
  rw [←List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  rw [show (600*step:ℚ)=600*step by rfl]
  norm_num only [Rat.cast_mul,Rat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact warm_term_semantics v0 step k j hv hs
 theorem checkWarm_sound {v0 step target : ℚ} {n : ℕ}
    (hv : 0 ≤ v0) (hs : 0 ≤ step) (hn : 0<n) (hc : checkWarm v0 step target n=true) :
    (target:ℝ) ≤ ∑k∈Finset.range n,600*(step:ℝ)*
      ∑j∈Finset.range 25,WinnerOldOuter.Warm.bandMass (30001/100) (1/500)
        (WinnerStrongEnvelope.data (v0:ℝ) (step:ℝ) k).Bl (warmM v0 step k j) j := by
  rw [checkWarm_eq] at hc
  have hh:=CH2QRH.DensityComputation.verify_upper _ 0 (n-1) (-target) cfg (by decide) hc
  simp only [Expr.eval,Finset.sum_neg_distrib,Rat.cast_neg] at hh
  rw [Icc_eq_range hn] at hh
  have hp : (target:ℝ) ≤ ∑k∈Finset.range n,Expr.eval (sumBodyRealEnv k) (warmBody v0 step) := by linarith
  simpa only [warm_body_semantics _ _ _ hv hs] using hp
#print axioms warm_body_semantics
#print axioms checkWarm_sound
#print axioms softMin_semantics
#print axioms warm_term_semantics
end WinnerStrongOuter
