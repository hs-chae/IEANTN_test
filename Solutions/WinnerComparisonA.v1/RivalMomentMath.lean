/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import LeanCert.Validity.Integration
import DensityCachedSum
import Mathlib.Tactic

namespace WinnerRivalMoments
open LeanCert.Core LeanCert.Engine MeasureTheory Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def moment (pos : Bool) (b : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  Real.exp ((if pos then b*y else -b*y)-(2371/10000)*Real.exp (if pos then 2*y else -2*y))*y^n

noncomputable def cellReal (upper pos : Bool) (b : ℝ) (n : ℕ) (l r : ℝ) : ℝ :=
  let linear := if upper then (if pos then r else -l) else (if pos then l else -r)
  let inner := if upper then (if pos then l else -r) else (if pos then r else -l)
  Real.exp (b*linear-(2371/10000)*Real.exp (2*inner))*(if upper then r else l)^n

theorem moment_continuous (pos : Bool) (b : ℝ) (n : ℕ) : Continuous (moment pos b n) := by
  cases pos <;> unfold moment <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop

theorem cell_bounds (pos : Bool) (b : ℝ) (n : ℕ) (l r y : ℝ)
    (hb : 0≤b) (hl : 0≤l) (hly : l≤y) (hyr : y≤r) :
    cellReal false pos b n l r≤moment pos b n y ∧
      moment pos b n y≤cellReal true pos b n l r := by
  have hy : 0≤y := hl.trans hly
  have hr : 0≤r := hy.trans hyr
  have hpL := pow_le_pow_left₀ hl hly n
  have hpR := pow_le_pow_left₀ hy hyr n
  cases pos
  · simp only [moment,cellReal,Bool.false_eq_true,ite_true,ite_false]
    constructor
    · apply mul_le_mul _ hpL (pow_nonneg hl n) (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      have he:=Real.exp_le_exp.mpr (show -2*y≤2*(-l) by linarith)
      nlinarith
    · apply mul_le_mul _ hpR (pow_nonneg hy n) (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      have he:=Real.exp_le_exp.mpr (show 2*(-r)≤-2*y by linarith)
      nlinarith
  · simp only [moment,cellReal,Bool.false_eq_true,ite_true,ite_false]
    constructor
    · apply mul_le_mul _ hpL (pow_nonneg hl n) (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      have he:=Real.exp_le_exp.mpr (show 2*y≤2*r by linarith)
      nlinarith
    · apply mul_le_mul _ hpR (pow_nonneg hy n) (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      have he:=Real.exp_le_exp.mpr (show 2*l≤2*y by linarith)
      nlinarith

theorem grid_bounds (pos : Bool) (b step : ℝ) (degree count : ℕ)
    (hb : 0≤b) (hstep : 0≤step) :
    (∑k∈Finset.range count,step*cellReal false pos b degree (step*k) (step*k+step))≤
      (∫y in (0:ℝ)..step*count,moment pos b degree y) ∧
    (∫y in (0:ℝ)..step*count,moment pos b degree y)≤
      ∑k∈Finset.range count,step*cellReal true pos b degree (step*k) (step*k+step) := by
  let edge : ℕ→ℝ := fun k=>step*k
  have hc := moment_continuous pos b degree
  have bounds : ∀k∈Finset.range count,
      step*cellReal false pos b degree (edge k) (edge (k+1))≤
        (∫y in edge k..edge (k+1),moment pos b degree y) ∧
      (∫y in edge k..edge (k+1),moment pos b degree y)≤
        step*cellReal true pos b degree (edge k) (edge (k+1)) := by
    intro k hk
    have hed : edge k≤edge (k+1) := by dsimp [edge];push_cast;nlinarith
    have hl : 0≤edge k := by dsimp [edge];positivity
    have h:=integral_bounds_of_bounds hed (hc.intervalIntegrable _ _)
      (fun y hy=>(cell_bounds pos b degree _ _ y hb hl hy.1 hy.2).1)
      (fun y hy=>(cell_bounds pos b degree _ _ y hb hl hy.1 hy.2).2)
    have hw : edge (k+1)-edge k=step := by dsimp [edge];push_cast;ring
    simpa [hw,mul_comm] using h
  have hlo:=Finset.sum_le_sum (fun k hk=>(bounds k hk).1)
  have hhi:=Finset.sum_le_sum (fun k hk=>(bounds k hk).2)
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun k _=>hc.intervalIntegrable (edge k) (edge (k+1)))] at hlo hhi
  simpa only [edge,Nat.cast_zero,mul_zero,Nat.cast_add,Nat.cast_one,mul_add,mul_one]
    using And.intro hlo hhi

def powExpr (x : Expr) : ℕ→Expr
  | 0 =>Expr.const 1
  | n+1 =>Expr.mul (powExpr x n) x

theorem powExpr_eval (x : Expr) (n : ℕ) (env : ℕ→ℝ) :
    Expr.eval env (powExpr x n)=Expr.eval env x^n := by
  induction n with
  |zero=>simp [powExpr,Expr.eval]
  |succ n ih=>simp [powExpr,Expr.eval,ih,pow_succ]

def cellExpr (upper pos : Bool) (b step : ℚ) (degree : ℕ) : Expr :=
  let l:=Expr.mul (Expr.const step) (Expr.var 0)
  let r:=Expr.add l (Expr.const step)
  let linear:=if upper then (if pos then r else Expr.neg l) else (if pos then l else Expr.neg r)
  let inner:=if upper then (if pos then l else Expr.neg r) else (if pos then r else Expr.neg l)
  Expr.mul (Expr.const step) (Expr.mul
    (Expr.exp (Expr.add (Expr.mul (Expr.const b) linear)
      (Expr.neg (Expr.mul (Expr.const (2371/10000)) (Expr.exp (Expr.mul (Expr.const 2) inner))))))
    (powExpr (if upper then r else l) degree))

theorem cell_semantics (upper pos : Bool) (b step : ℚ) (degree k : ℕ) :
    Expr.eval (sumBodyRealEnv k) (cellExpr upper pos b step degree)=
      (step:ℝ)*cellReal upper pos b degree ((step:ℝ)*k) ((step:ℝ)*k+step) := by
  cases upper <;> cases pos
  all_goals
    simp only [cellExpr,cellReal,Expr.eval,powExpr_eval,sumBodyRealEnv,
      Bool.false_eq_true,ite_true,ite_false]
    push_cast
    ring

theorem Icc_zero_eq_range (n : ℕ) (hn : 0<n) :
    Finset.Icc 0 (n-1)=Finset.range n := by
  ext k
  simp only [Finset.mem_Icc,Finset.mem_range]
  omega

theorem integral_bounds_from_checks (pos : Bool) (b step lo hi : ℚ) (degree count : ℕ)
    (hb : 0≤b) (hstep : 0≤step) (hcount : 0<count) (cfg : DyadicConfig)
    (hprec : cfg.precision≤0)
    (hlo : CH2QRH.DensityComputation.checkUpperBound
      (Expr.neg (cellExpr false pos b step degree)) 0 (count-1) (-lo) cfg=true)
    (hhi : CH2QRH.DensityComputation.checkUpperBound
      (cellExpr true pos b step degree) 0 (count-1) hi cfg=true) :
    (lo:ℝ)≤(∫y in (0:ℝ)..((step:ℝ)*count),moment pos b degree y) ∧
      (∫y in (0:ℝ)..((step:ℝ)*count),moment pos b degree y)≤hi := by
  have hbl : (0:ℝ)≤b := by exact_mod_cast hb
  have hsl : (0:ℝ)≤step := by exact_mod_cast hstep
  have hg:=grid_bounds pos b step degree count hbl hsl
  have hl:=CH2QRH.DensityComputation.verify_upper _ 0 (count-1) (-lo) cfg hprec hlo
  have hh:=CH2QRH.DensityComputation.verify_upper _ 0 (count-1) hi cfg hprec hhi
  rw [Icc_zero_eq_range count hcount] at hl hh
  simp only [Expr.eval,cell_semantics,Finset.sum_neg_distrib,Rat.cast_neg] at hl hh
  exact ⟨by linarith [hg.1],hg.2.trans hh⟩

#print axioms integral_bounds_from_checks
end WinnerRivalMoments
