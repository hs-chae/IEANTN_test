/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.Ray
import WinnerProgramA.Program
import WinnerProgramA.Semantics
import Lean
open LeanCert.Core LeanCert.Engine
namespace WinnerDensityA
namespace Program
open WinnerProgramA
abbrev lit := Expr.const
abbrev add := Expr.add
abbrev mul := Expr.mul
abbrev sub := WinnerProgramA.sub
abbrev dv := WinnerProgramA.divE
abbrev pw := WinnerProgramA.powE

def envelopeExpr (c d : ℚ) (s : Expr) (τ : ℚ) : Expr :=
  let a := dv (sub (mul (lit 8) s) (lit 5)) (lit 3)
  let q := sub (lit 5) (mul (lit 2) s)
  add (mul (lit 2) (WinnerProgramA.moment s c d))
    (mul (mul (lit 4) (.namedConst .pi))
      (add (mul (lit c) (Expr.exp (add (.neg (mul a (lit τ))) (mul q (Expr.log (lit τ))))))
        (mul (lit (d*τ^2)) (Expr.exp (lit (-τ))))))

noncomputable def expEnvelope (c d s τ : ℝ) :=
  2*WinnerProgramA.momentReal s c d + 4*Real.pi*
    (c*Real.exp (-((8*s-5)/3)*τ+(5-2*s)*Real.log τ)+d*τ^2*Real.exp (-τ))

theorem envelope_semantics (c d τ : ℚ) (s : Expr) (env : ℕ → ℝ) :
    Expr.eval env (envelopeExpr c d s τ)=expEnvelope c d (Expr.eval env s) τ := by
  simp only [envelopeExpr,Expr.eval,WinnerProgramA.moment_semantics,lit,add,mul,sub,dv,
    WinnerProgramA.sub,WinnerProgramA.divE,LeanCert.Core.MathConst.toReal,expEnvelope]
  push_cast
  ring

theorem envelope_real (c d s τ : ℝ) (hτ : 0<τ) :
    expEnvelope c d s τ=envelope c d s τ := by
  have hH : 0<H := by norm_num [H]
  have hlH : 0<Real.log H := Real.log_pos (by norm_num [H])
  have hr : 1-8*(1-s)/3=(8*s-5)/3 := by ring
  have hmain : H^(8*(1-s)/3-1)*Real.log H^(5-2*s)=
      Real.exp (-((8*s-5)/3)*Real.log H+(5-2*s)*Real.log (Real.log H)) := by
    rw [Real.rpow_def_of_pos hH,Real.rpow_def_of_pos hlH,←Real.exp_add]
    congr 1;ring
  have hheight : Real.exp τ^(8*(1-s)/3)*τ^(5-2*s)/Real.exp τ=
      Real.exp (-((8*s-5)/3)*τ+(5-2*s)*Real.log τ) := by
    rw [←Real.exp_mul,Real.rpow_def_of_pos hτ,←Real.exp_add,←Real.exp_sub]
    congr 1;ring
  have hF : poly c d s (Real.exp τ)/Real.exp τ=
      c*Real.exp (-((8*s-5)/3)*τ+(5-2*s)*Real.log τ)+d*τ^2*Real.exp (-τ) := by
    unfold poly
    rw [Real.log_exp]
    calc
      _ = c*(Real.exp τ^(8*(1-s)/3)*τ^(5-2*s)/Real.exp τ)+d*τ^2*(1/Real.exp τ) := by ring
      _ = _ := by rw [hheight,Real.exp_neg,one_div]
  unfold expEnvelope envelope moment CH2QRH.densityMomentMain WinnerProgramA.momentReal
  dsimp only
  rw [hr,hmain,hF]
  norm_num only [H]
  ring

noncomputable def uniformGrid (n : ℕ) (k : ℕ) : ℝ := 3/4+(k:ℝ)/(8*n)
theorem grid_monotone {n : ℕ} (hn : 0<n) : Monotone (uniformGrid n) := by
  intro i j hij
  dsimp [uniformGrid]
  gcongr

def baseExpr (c d L τ : ℚ) : Expr :=
  add (mul (Expr.exp (lit (-L/8))) (envelopeExpr c d (lit (3/4)) τ))
    (add (mul (Expr.exp (lit (-L/8)))
      (add (dv (pw (lit (τ+1/10^9)) 2) (mul (lit 2) (.namedConst .pi)))
        (mul (add (lit 2) (dv (lit 1) (.namedConst .pi))) (lit (τ+1/10^9)))))
      (lit (1/10^12)))
def termExpr (c d L τ : ℚ) (n : ℕ) : Expr :=
  let s := add (lit (3/4)) (dv (.var 0) (lit (8*n)))
  let r := add s (lit (1/(8*n)))
  mul (sub (Expr.exp (mul (lit L) (sub r (lit (7/8)))))
      (Expr.exp (mul (lit L) (sub s (lit (7/8)))))) (envelopeExpr c d s τ)
def program (c d L τ : ℚ) (n : ℕ) : List WinnerProgramA.Row :=
  [⟨baseExpr c d L τ,1⟩,⟨termExpr c d L τ n,n⟩]

theorem program_semantics (c d L τ : ℚ) {n : ℕ} (hn : 0<n) (hτ : 0<(τ:ℝ)) :
    WinnerProgramA.value (program c d L τ n)=
      rowCoefficient (fun _ ↦ c) (fun _ ↦ d) (uniformGrid n) n L τ := by
  have hset : Finset.Icc 0 (n-1)=Finset.range n := by ext k;simp only [Finset.mem_Icc,Finset.mem_range];omega
  simp only [WinnerProgramA.value,program,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,WinnerProgramA.rowValue,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton,hset]
  have hbase : Expr.eval (sumBodyRealEnv 0) (baseExpr c d L τ)=
      Real.exp (-(L:ℝ)/8)*envelope c d (3/4) τ+
      Real.exp (-(L:ℝ)/8)*(((τ:ℝ)+1/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((τ:ℝ)+1/10^9))+1/10^12 := by
    simp only [baseExpr,Expr.eval,envelope_semantics,lit,add,mul,sub,dv,pw,
      WinnerProgramA.sub,WinnerProgramA.divE,WinnerProgramA.powE,LeanCert.Core.MathConst.toReal]
    push_cast
    rw [envelope_real _ _ _ _ hτ]
    ring
  rw [hbase]
  unfold rowCoefficient gridCoefficient
  have hterms : (∑ k ∈ Finset.range n,Expr.eval (sumBodyRealEnv k) (termExpr c d L τ n))=
      ∑ k ∈ Finset.range n,
        (Real.exp ((L:ℝ)*(uniformGrid n (k+1)-7/8))-Real.exp ((L:ℝ)*(uniformGrid n k-7/8)))*
          envelope c d (uniformGrid n k) τ := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [termExpr,Expr.eval,envelope_semantics,sumBodyRealEnv,lit,add,mul,sub,dv,
      WinnerProgramA.sub,WinnerProgramA.divE]
    push_cast
    rw [envelope_real _ _ _ _ hτ]
    dsimp [uniformGrid]
    push_cast
    congr 2 <;> congr 1 <;> ring
  rw [hterms]
  simp only [uniformGrid,Nat.cast_zero,zero_div,add_zero]
  rw [show (L:ℝ)*((3/4:ℝ)-7/8)=-(L:ℝ)/8 by ring]
  ring
end Program
end WinnerDensityA
#print axioms WinnerDensityA.Program.program_semantics
