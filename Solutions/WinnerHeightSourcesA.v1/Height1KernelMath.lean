/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LeanCert.Validity.Integration
import DensityCachedSum
import Mathlib.Tactic
import Lean

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WinnerHeightKernel1
open LeanCert.Core LeanCert.Engine MeasureTheory
abbrev lit := Expr.const
abbrev add := Expr.add
abbrev mul := Expr.mul
abbrev neg := Expr.neg
def sub (a b : Expr) := add a (neg b)
def dv (a b : Expr) := mul a (.inv b)
def sq (a : Expr) := mul a a
def rt (a : Expr) := Expr.exp (dv (Expr.log a) (lit 2))

def kernelExpr (sign : ℚ) : Expr :=
  let y := Expr.var 0
  let weight := Expr.exp (sub (mul (lit 2) y)
    (mul (lit (601/2500)) (Expr.exp (mul (lit 2) y))))
  let first := mul (rt (add (mul (lit (643179/1000000)) (Expr.exp y)) (lit (43091/500000))))
    (add (mul (Expr.exp (dv y (lit 6)))
      (add (lit 1) (dv (mul (lit sign) y) (lit (29729633/1000000))))) (lit (109037/100000000)))
  mul weight (sq (add first (mul (lit (7117/100000000)) (Expr.exp (dv y (lit 2))))))

noncomputable def kernelReal (sign y : ℝ) : ℝ :=
  Real.exp (2*y-(601/2500)*Real.exp (2*y)) *
    (Real.sqrt ((643179/1000000)*Real.exp y+43091/500000) *
      (Real.exp (y/6)*(1+sign*y/(29729633/1000000))+109037/100000000) +
      (7117/100000000)*Real.exp (y/2))^2

theorem kernel_semantics (sign : ℚ) (env : ℕ → ℝ) :
    Expr.eval env (kernelExpr sign) = kernelReal sign (env 0) := by
  simp only [kernelExpr,kernelReal,Expr.eval,lit,add,mul,sub,neg,dv,sq,rt]
  push_cast
  have hr : Real.exp (Real.log ((643179/1000000:ℝ)*Real.exp (env 0)+43091/500000)/2) =
      Real.sqrt ((643179/1000000:ℝ)*Real.exp (env 0)+43091/500000) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  simp only [div_eq_mul_inv] at hr ⊢
  rw [hr]
  ring

theorem kernel_continuous (sign : ℝ) : Continuous (kernelReal sign) := by
  unfold kernelReal
  fun_prop


#print axioms kernel_semantics
end WinnerHeightKernel1

namespace WinnerHeightKernel1
open LeanCert.Core LeanCert.Engine MeasureTheory Set

def cellExpr (sign start step : ℚ) : Expr :=
  let l := add (lit start) (mul (lit step) (.var 0))
  let r := add l (lit step)
  let endpoint := if sign = 1 then r else l
  let weight := Expr.exp (sub (mul (lit 2) r)
    (mul (lit (601/2500)) (Expr.exp (mul (lit 2) l))))
  let first := mul (rt (add (mul (lit (643179/1000000)) (Expr.exp r)) (lit (43091/500000))))
    (add (mul (Expr.exp (dv r (lit 6)))
      (add (lit 1) (dv (mul (lit sign) endpoint) (lit (29729633/1000000))))) (lit (109037/100000000)))
  mul (lit step) (mul weight (sq (add first
    (mul (lit (7117/100000000)) (Expr.exp (dv r (lit 2)))))))

noncomputable def cellReal (sign l r : ℝ) : ℝ :=
  Real.exp (2*r-(601/2500)*Real.exp (2*l))*
    (Real.sqrt ((643179/1000000)*Real.exp r+43091/500000)*
      (Real.exp (r/6)*(1+sign*(if sign=1 then r else l)/(29729633/1000000))+109037/100000000)+
      (7117/100000000)*Real.exp (r/2))^2

theorem cell_semantics (sign start step : ℚ) (k : ℕ) :
    Expr.eval (sumBodyRealEnv k) (cellExpr sign start step) =
      (step:ℝ)*cellReal sign ((start:ℝ)+(step:ℝ)*k) ((start:ℝ)+(step:ℝ)*k+step) := by
  have hreal : ((sign:ℝ)=1) ↔ sign=1 := by norm_cast
  simp only [cellExpr,cellReal,Expr.eval,lit,add,mul,sub,neg,dv,sq,rt,sumBodyRealEnv,hreal]
  push_cast
  split_ifs with hs
  all_goals
    simp only [Expr.eval,sumBodyRealEnv]
    push_cast
    have hr : Real.exp (Real.log ((643179/1000000:ℝ)*Real.exp ((start:ℝ)+(step:ℝ)*k+step)+43091/500000)/2) =
        Real.sqrt ((643179/1000000:ℝ)*Real.exp ((start:ℝ)+(step:ℝ)*k+step)+43091/500000) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
      congr 1
      ring
    simp only [div_eq_mul_inv] at hr ⊢
    rw [hr]
    ring

theorem kernel_cell_bound (sign l r y : ℝ)
    (hsgn : sign=0 ∨ sign=1) (hly : l ≤ y) (hyr : y ≤ r)
    (hside : if sign=1 then 0 ≤ l else r ≤ 0) :
    kernelReal sign y ≤ cellReal sign l r := by
  have hey : Real.exp y ≤ Real.exp r := Real.exp_le_exp.mpr hyr
  have he6 : Real.exp (y/6) ≤ Real.exp (r/6) := Real.exp_le_exp.mpr (by linarith)
  have he2 : Real.exp (y/2) ≤ Real.exp (r/2) := Real.exp_le_exp.mpr (by linarith)
  have hfac0 : 0 ≤ 1+sign*y/(29729633/1000000) := by
    rcases hsgn with rfl|rfl <;> norm_num at hside ⊢ <;> linarith
  have hfac : 1+sign*y/(29729633/1000000) ≤ 1+sign*(if sign=1 then r else l)/(29729633/1000000) := by
    rcases hsgn with rfl|rfl <;> norm_num <;> linarith
  have hfacr : 0 ≤ 1+sign*(if sign=1 then r else l)/(29729633/1000000) := hfac0.trans hfac
  have hs : Real.sqrt ((643179/1000000:ℝ)*Real.exp y+43091/500000) ≤
      Real.sqrt ((643179/1000000:ℝ)*Real.exp r+43091/500000) := by gcongr
  have hin0 : 0 ≤ Real.sqrt ((643179/1000000:ℝ)*Real.exp y+43091/500000)*
      (Real.exp (y/6)*(1+sign*y/(29729633/1000000))+109037/100000000)+(7117/100000000)*Real.exp (y/2) := by positivity
  have hin : Real.sqrt ((643179/1000000:ℝ)*Real.exp y+43091/500000)*
      (Real.exp (y/6)*(1+sign*y/(29729633/1000000))+109037/100000000)+(7117/100000000)*Real.exp (y/2) ≤
      Real.sqrt ((643179/1000000:ℝ)*Real.exp r+43091/500000)*
      (Real.exp (r/6)*(1+sign*(if sign=1 then r else l)/(29729633/1000000))+109037/100000000)+(7117/100000000)*Real.exp (r/2) := by gcongr
  have hweight : Real.exp (2*y-(601/2500)*Real.exp (2*y)) ≤
      Real.exp (2*r-(601/2500)*Real.exp (2*l)) := by
    apply Real.exp_le_exp.mpr
    have hlow : Real.exp (2*l) ≤ Real.exp (2*y) := Real.exp_le_exp.mpr (by linarith)
    nlinarith
  unfold kernelReal cellReal
  gcongr

theorem kernel_grid_integral_bound (sign a step : ℝ) (n : ℕ)
    (hstep : 0 ≤ step) (hsgn : sign=0 ∨ sign=1)
    (hside : if sign=1 then 0 ≤ a else a+step*n ≤ 0) :
    (∫ y in a..(a+step*n), kernelReal sign y) ≤
      ∑ k ∈ Finset.range n, step*cellReal sign (a+step*k) (a+step*k+step) := by
  let edge : ℕ → ℝ := fun k => a+step*k
  have hc := kernel_continuous sign
  have hb : ∀ k ∈ Finset.range n,
      (∫ y in edge k..edge (k+1), kernelReal sign y) ≤
        step*cellReal sign (edge k) (edge (k+1)) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hed : edge k ≤ edge (k+1) := by dsimp [edge]; push_cast; nlinarith
    have hs : if sign=1 then 0 ≤ edge k else edge (k+1) ≤ 0 := by
      split_ifs with hh
      · simp [hh] at hside
        dsimp [edge]
        positivity
      · simp [hh] at hside
        have hkn : (k+1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : k+1≤n)
        dsimp [edge]
        push_cast
        nlinarith
    have hp := LeanCert.Engine.integral_bounds_of_bounds hed (hc.intervalIntegrable _ _)
      (lo:=0) (hi:=cellReal sign (edge k) (edge (k+1)))
      (fun y _ => by unfold kernelReal; positivity)
      (fun y hy => kernel_cell_bound sign (edge k) (edge (k+1)) y hsgn hy.1 hy.2 hs)
    have hw : edge (k+1)-edge k=step := by dsimp [edge]; push_cast; ring
    simpa [hw,mul_comm] using hp.2
  have hs := Finset.sum_le_sum hb
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => hc.intervalIntegrable (edge k) (edge (k+1)))] at hs
  simpa only [edge,Nat.cast_zero,mul_zero,add_zero,Nat.cast_add,Nat.cast_one,
    mul_add,mul_one,add_assoc] using hs


#print axioms kernel_cell_bound
#print axioms kernel_grid_integral_bound
end WinnerHeightKernel1
