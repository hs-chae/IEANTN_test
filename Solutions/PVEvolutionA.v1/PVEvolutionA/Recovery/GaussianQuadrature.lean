/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.GaussianReduction
import WinnerProgramA.Program
import LeanCert.Validity.Integration

namespace PVEvolutionA.Recovery.Gaussian
open Real Set MeasureTheory LeanCert.Core LeanCert.Engine
set_option maxHeartbeats 0

theorem basis_exp (n k : ℕ) (y : ℝ) :
    basis n k y = exp ((2+(n:ℝ)/6)*y-(601/2500)*exp (2*y))*y^k := by
  unfold basis weight
  rw [← exp_nat_mul, ← exp_add]
  congr 1
  congr 1
  push_cast
  ring

theorem basis_continuous (n k : ℕ) : Continuous (basis n k) := by
  unfold basis weight
  fun_prop

noncomputable def cell (n k : ℕ) (l r : ℝ) : ℝ :=
  exp ((2+(n:ℝ)/6)*r-(601/2500)*exp (2*l))*r^k

theorem basis_cell (n k : ℕ) {l r y : ℝ} (hly : l ≤ y) (hyr : y ≤ r)
    (hside : k=0 ∨ 0≤l) : basis n k y ≤ cell n k l r := by
  have hrate : 0 ≤ 2+(n:ℝ)/6 := by positivity
  have hexp : exp ((2+(n:ℝ)/6)*y-(601/2500)*exp (2*y)) ≤
      exp ((2+(n:ℝ)/6)*r-(601/2500)*exp (2*l)) := by
    apply exp_le_exp.mpr
    have hl := exp_le_exp.mpr (by linarith : 2*l≤2*y)
    have hu := mul_le_mul_of_nonneg_left hyr hrate
    nlinarith
  rw [basis_exp]
  unfold cell
  rcases hside with rfl | hl
  · simpa only [pow_zero,mul_one] using hexp
  · have hy0 : 0≤y := hl.trans hly
    have hp : y^k≤r^k := pow_le_pow_left₀ hy0 hyr k
    exact mul_le_mul hexp hp (pow_nonneg hy0 k) (exp_pos _).le

theorem basis_grid (n k : ℕ) (a step : ℝ) (count : ℕ)
    (hstep : 0≤step) (hside : k=0 ∨ 0≤a) :
    (∫ y in a..(a+step*count), basis n k y) ≤
      ∑ i ∈ Finset.range count, step*cell n k (a+step*i) (a+step*i+step) := by
  let edge : ℕ→ℝ := fun i => a+step*i
  have hc := basis_continuous n k
  have hb : ∀ i∈Finset.range count,
      (∫ y in edge i..edge (i+1),basis n k y) ≤ step*cell n k (edge i) (edge (i+1)) := by
    intro i hi
    have hed : edge i≤edge (i+1) := by dsimp [edge];push_cast;nlinarith
    have hs : k=0 ∨ 0≤edge i := by
      rcases hside with hk | ha
      · exact Or.inl hk
      · right;dsimp [edge];positivity
    have hy0 : ∀y∈Icc (edge i) (edge (i+1)),0≤basis n k y := by
      intro y hy
      unfold basis weight
      rcases hs with rfl | hh
      · positivity
      · have hy0 : 0≤y := hh.trans hy.1
        positivity
    have hh := integral_bounds_of_bounds hed (hc.intervalIntegrable _ _) hy0
      (fun y hy => basis_cell n k hy.1 hy.2 hs)
    have hw : edge (i+1)-edge i=step := by dsimp [edge];push_cast;ring
    simpa only [hw,mul_comm] using hh.2
  have hsum := Finset.sum_le_sum hb
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun i _ => hc.intervalIntegrable (edge i) (edge (i+1)))] at hsum
  simpa only [edge,Nat.cast_zero,mul_zero,add_zero,Nat.cast_add,Nat.cast_one,
    mul_add,mul_one,add_assoc] using hsum

def power (e : Expr) : ℕ→Expr
  | 0 => .const 1
  | n+1 => .mul e (power e n)

theorem power_eval (e : Expr) (env : ℕ→ℝ) (n : ℕ) :
    Expr.eval env (power e n) = Expr.eval env e ^ n := by
  induction n with
  | zero => simp [power,Expr.eval]
  | succ n ih => simp only [power,Expr.eval,ih,pow_succ];ring

/-- A row's exact dyadic evaluator encloses this explicit endpoint majorant.
There are no variable logarithm, inverse or square-root domains in this program. -/
def cellExpr (n k : ℕ) (a step : ℚ) : Expr :=
  let l := Expr.add (.const a) (.mul (.const step) (.var 0))
  let r := Expr.add l (.const step)
  let w := Expr.exp (.add (.mul (.const (2+(n:ℚ)/6)) r)
    (.neg (.mul (.const (601/2500)) (.exp (.mul (.const 2) l)))))
  .mul (.const step) (.mul w (power r k))

theorem cellExpr_eval (n k i : ℕ) (a step : ℚ) :
    Expr.eval (sumBodyRealEnv i) (cellExpr n k a step) =
      (step:ℝ)*cell n k ((a:ℝ)+(step:ℝ)*i) ((a:ℝ)+(step:ℝ)*i+step) := by
  simp only [cellExpr,Expr.eval,power_eval,sumBodyRealEnv,cell]
  push_cast
  ring

#print axioms basis_grid
#print axioms cellExpr_eval
end PVEvolutionA.Recovery.Gaussian
