/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.Program
namespace WinnerDensityA
namespace ModelProgram
open LeanCert.Core LeanCert.Engine
open WinnerDensityA.Program
noncomputable def modelC (κ B s : ℝ) := κ*Real.exp (B*(s-7/8))

def modelEnvelopeExpr (κ B d : ℚ) (s : Expr) (τ : ℚ) : Expr :=
  let c := mul (lit κ) (Expr.exp (mul (lit B) (sub s (lit (7/8)))))
  add (mul c (envelopeExpr 1 0 s τ)) (mul (lit d) (envelopeExpr 0 1 s τ))

theorem model_envelope_semantics (κ B d τ : ℚ) (hτ : 0<(τ:ℝ)) (s : Expr) (env : ℕ → ℝ) :
    Expr.eval env (modelEnvelopeExpr κ B d s τ)=
      envelope (modelC κ B (Expr.eval env s)) d (Expr.eval env s) τ := by
  simp only [modelEnvelopeExpr,Expr.eval,Program.envelope_semantics,lit,add,mul,sub,
    WinnerProgramA.sub,modelC]
  push_cast
  rw [Program.envelope_real _ _ _ _ hτ,Program.envelope_real _ _ _ _ hτ]
  unfold envelope moment poly
  ring

def base (κ B d L τ : ℚ) : Expr :=
  add (mul (Expr.exp (lit (-L/8))) (modelEnvelopeExpr κ B d (lit (3/4)) τ))
    (Program.baseExpr 0 0 L τ)
def term (κ B d L τ : ℚ) (n : ℕ) : Expr :=
  let s := add (lit (3/4)) (dv (.var 0) (lit (8*n)))
  let r := add s (lit (1/(8*n)))
  mul (sub (Expr.exp (mul (lit L) (sub r (lit (7/8)))))
      (Expr.exp (mul (lit L) (sub s (lit (7/8)))))) (modelEnvelopeExpr κ B d s τ)
def program (κ B d L τ : ℚ) (n : ℕ) : List WinnerProgramA.Row :=
  [⟨base κ B d L τ,1⟩,⟨term κ B d L τ n,n⟩]

theorem program_semantics (κ B d L τ : ℚ) {n : ℕ} (hn : 0<n) (hτ : 0<(τ:ℝ)) :
    WinnerProgramA.value (program κ B d L τ n)=
      rowCoefficient (modelC κ B) (fun _ ↦ d) (uniformGrid n) n L τ := by
  have hset : Finset.Icc 0 (n-1)=Finset.range n := by ext k;simp only [Finset.mem_Icc,Finset.mem_range];omega
  simp only [WinnerProgramA.value,program,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,WinnerProgramA.rowValue,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton,hset]
  have hbase : Expr.eval (sumBodyRealEnv 0) (base κ B d L τ)=
      Real.exp (-(L:ℝ)/8)*envelope (modelC κ B (3/4)) d (3/4) τ+
      Real.exp (-(L:ℝ)/8)*(((τ:ℝ)+1/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((τ:ℝ)+1/10^9))+1/10^12 := by
    simp only [base,Expr.eval,model_envelope_semantics _ _ _ _ hτ,Program.baseExpr,
      Program.envelope_semantics,lit,add,mul,sub,dv,pw,WinnerProgramA.sub,
      WinnerProgramA.divE,WinnerProgramA.powE,LeanCert.Core.MathConst.toReal]
    push_cast
    unfold Program.expEnvelope WinnerProgramA.momentReal
    dsimp only
    ring
  rw [hbase]
  unfold rowCoefficient gridCoefficient
  have hterms : (∑ k ∈ Finset.range n,Expr.eval (sumBodyRealEnv k) (term κ B d L τ n))=
      ∑ k ∈ Finset.range n,
        (Real.exp ((L:ℝ)*(uniformGrid n (k+1)-7/8))-Real.exp ((L:ℝ)*(uniformGrid n k-7/8)))*
          envelope (modelC κ B (uniformGrid n k)) d (uniformGrid n k) τ := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [term,Expr.eval,model_envelope_semantics _ _ _ _ hτ,sumBodyRealEnv,lit,add,mul,sub,dv,
      WinnerProgramA.sub,WinnerProgramA.divE]
    push_cast
    dsimp [uniformGrid]
    push_cast
    congr 2 <;> congr 1 <;> ring
  rw [hterms]
  simp only [uniformGrid,Nat.cast_zero,zero_div,add_zero]
  rw [show (L:ℝ)*((3/4:ℝ)-7/8)=-(L:ℝ)/8 by ring]
  ring
end ModelProgram
end WinnerDensityA
#print axioms WinnerDensityA.ModelProgram.program_semantics
