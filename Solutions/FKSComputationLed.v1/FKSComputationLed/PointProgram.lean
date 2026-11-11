/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import LeanCert.Engine.IntervalEvalDyadic
import Mathlib
import FKSComputationLed.Support.LiTaylor
open LeanCert.Core LeanCert.Engine
namespace FKSComputationLed.PointProgram

def cfg : DyadicConfig := { precision := -384, taylorDepth := 24 }
def ctx := LeanCert.Internal.Dyadic.prepareContext cfg

def coeffs : List ℚ := (List.range 79).map fun k =>
  1 / (((k+1:ℕ):ℚ)*(Nat.factorial (k+1):ℚ))
def hornerExpr : List ℚ → Expr
  | [] => .const 0
  | c::cs => .add (.const c) (.mul (.var 0) (hornerExpr cs))
def primitiveExpr : Expr := .add (.log (.var 0)) (.mul (.var 0) (hornerExpr coeffs))
def hornerReal (cs : List ℚ) (y : ℝ) : ℝ :=
  cs.foldr (fun (c:ℚ) (v:ℝ) => (c:ℝ)+y*v) (0:ℝ)
lemma eval_horner (cs : List ℚ) (ρ : Nat→ℝ) :
    Expr.eval ρ (hornerExpr cs) = hornerReal cs (ρ 0) := by
  induction cs with
  | nil => simp [hornerExpr,hornerReal,Expr.eval]
  | cons c cs ih => simpa [hornerExpr,hornerReal,Expr.eval] using congrArg (fun t => (c:ℝ)+(ρ 0)*t) ih
lemma horner_sum (cs : List ℚ) (y : ℝ) :
    hornerReal cs y = ∑ k∈Finset.range cs.length, ((cs[k]!:ℚ):ℝ)*y^k := by
  induction cs with
  | nil => simp [hornerReal]
  | cons c cs ih =>
    simp only [hornerReal,List.foldr_cons] at *
    simp only [List.length_cons]
    rw [ih,Finset.sum_range_succ']
    simp only [List.getElem!_cons_zero,pow_zero,mul_one]
    rw [Finset.mul_sum,add_comm (c:ℝ)]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k<cs.length := Finset.mem_range.mp hk
    simp only [List.getElem!_cons_succ,pow_succ]
    ring

lemma coeffs_length : coeffs.length=79 := by simp [coeffs]
lemma coeffs_get (k : Nat) (hk : k<79) :
    coeffs[k]! = 1 / (((k+1:ℕ):ℚ)*(Nat.factorial (k+1):ℚ)) := by
  have h : k<coeffs.length := by simpa [coeffs] using hk
  rw [getElem!_pos coeffs k h]
  simp [coeffs]
lemma primitiveExpr_value (ρ : Nat→ℝ) :
    Expr.eval ρ primitiveExpr = LiTaylor.primitive 79 (ρ 0) := by
  simp only [primitiveExpr,Expr.eval_add,Expr.eval_log,Expr.eval_var,Expr.eval_mul]
  rw [eval_horner,horner_sum,coeffs_length]
  unfold LiTaylor.primitive
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeffs_get k (Finset.mem_range.mp hk)]
  push_cast
  rw [pow_succ]
  ring

abbrev run (e : Expr) (I : IntervalDyadic) :=
  LeanCert.Internal.Dyadic.evalPreparedCached e (fun _=>I) ctx

def integerInterval (n : Nat) : IntervalDyadic := IntervalDyadic.singleton (LeanCert.Core.Dyadic.ofInt n)
def logPoint (n : Nat) := run (.log (.var 0)) (integerInterval n)
def primitivePoint (n : Nat) := run primitiveExpr (logPoint n).1

def sample (n : Nat) :=
  let l := logPoint n
  let f := primitivePoint n
  (l.2 && f.2,l.1.toIntervalRat,f.1.toIntervalRat)
#eval sample 100000000
#print axioms eval_horner
end FKSComputationLed.PointProgram
