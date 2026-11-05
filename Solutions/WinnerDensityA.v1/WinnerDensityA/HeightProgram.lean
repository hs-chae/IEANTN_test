/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.HeightExpression
namespace WinnerDensityA.HeightProgram
open Real LeanCert.Core LeanCert.Engine WinnerDensityA.Program WinnerDensityA.HeightExpression
set_option maxHeartbeats 0

def correctionExpr (s : Expr) : Expr :=
  add (add (mul (lit (233/10000)) (lowerExpr s 1))
    (mul (lit (43/2000)) (lowerExpr s 2))) (mul (lit (49/1250)) (lowerExpr s 4))
def envelopeExpr (s : Expr) (τ : ℚ) : Expr :=
  sub (ModelProgram.modelEnvelopeExpr (72931/10000) (54281/10000) 6 s τ)
    (mul (mul (lit 2) (.exp (mul (lit (54281/10000)) (sub s (lit (7/8)))))) (correctionExpr s))
noncomputable def correction (s : ℝ) :=
  (233/10000)*lowerExp s (log H+1)+(43/2000)*lowerExp s (log H+2)+
    (49/1250)*lowerExp s (log H+4)
noncomputable def mathEnvelope (s τ : ℝ) :=
  WinnerDensityA.envelope (ModelProgram.modelC (72931/10000) (54281/10000) s) 6 s τ-
    2*exp ((54281/10000)*(s-7/8))*correction s

theorem correction_semantics (s : Expr) (env : ℕ→ℝ) :
    Expr.eval env (correctionExpr s)=correction (Expr.eval env s) := by
  simp only [correctionExpr,Expr.eval,lower_semantics,lit,add,mul,correction]
  push_cast
  ring

theorem envelope_semantics (s : Expr) (τ : ℚ) (env : ℕ→ℝ) (hτ : 0<(τ:ℝ)) :
    Expr.eval env (envelopeExpr s τ)=mathEnvelope (Expr.eval env s) τ := by
  simp only [envelopeExpr,Expr.eval,ModelProgram.model_envelope_semantics _ _ _ _ hτ,
    correction_semantics,lit,sub,mul,WinnerProgramA.sub,mathEnvelope]
  push_cast
  ring

noncomputable def rowCoefficient (n : ℕ) (L τ : ℝ) :=
  gridCoefficient (fun s=>mathEnvelope s τ) (uniformGrid n) n L+
    exp (-L/8)*((τ+1/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*(τ+1/10^9))+1/10^12

def base (L τ : ℚ) : Expr :=
  add (mul (.exp (lit (-L/8))) (envelopeExpr (lit (3/4)) τ)) (Program.baseExpr 0 0 L τ)
def term (L τ : ℚ) (n : ℕ) : Expr :=
  let s:=add (lit (3/4)) (dv (.var 0) (lit (8*n)))
  let r:=add s (lit (1/(8*n)))
  mul (sub (.exp (mul (lit L) (sub r (lit (7/8)))))
    (.exp (mul (lit L) (sub s (lit (7/8)))))) (envelopeExpr s τ)
def program (L τ : ℚ) (n : ℕ) : List WinnerProgramA.Row :=
  [⟨base L τ,1⟩,⟨term L τ n,n⟩]

theorem program_semantics (L τ : ℚ) {n : ℕ} (hn : 0<n) (hτ : 0<(τ:ℝ)) :
    WinnerProgramA.value (program L τ n)=rowCoefficient n L τ := by
  have hset : Finset.Icc 0 (n-1)=Finset.range n := by ext k;simp only [Finset.mem_Icc,Finset.mem_range];omega
  simp only [WinnerProgramA.value,program,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,WinnerProgramA.rowValue,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton,hset]
  have hbase : Expr.eval (sumBodyRealEnv 0) (base L τ)=
      exp (-(L:ℝ)/8)*mathEnvelope (3/4) τ+
      exp (-(L:ℝ)/8)*(((τ:ℝ)+1/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((τ:ℝ)+1/10^9))+1/10^12 := by
    simp only [base,Expr.eval,envelope_semantics _ _ _ hτ,Program.baseExpr,
      Program.envelope_semantics,lit,add,mul,sub,dv,pw,WinnerProgramA.sub,
      WinnerProgramA.divE,WinnerProgramA.powE,LeanCert.Core.MathConst.toReal]
    push_cast
    unfold Program.expEnvelope WinnerProgramA.momentReal
    dsimp only
    ring
  rw [hbase]
  unfold rowCoefficient gridCoefficient
  have hterms : (∑ k∈Finset.range n,Expr.eval (sumBodyRealEnv k) (term L τ n))=
      ∑ k∈Finset.range n,
        (exp ((L:ℝ)*(uniformGrid n (k+1)-7/8))-exp ((L:ℝ)*(uniformGrid n k-7/8)))*
          mathEnvelope (uniformGrid n k) τ := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [term,Expr.eval,envelope_semantics _ _ _ hτ,sumBodyRealEnv,lit,add,mul,sub,dv,
      WinnerProgramA.sub,WinnerProgramA.divE]
    push_cast
    dsimp [uniformGrid]
    push_cast
    congr 2 <;> congr 1 <;> ring
  rw [hterms]
  simp only [uniformGrid,Nat.cast_zero,zero_div,add_zero]
  rw [show (L:ℝ)*((3/4:ℝ)-7/8)=-(L:ℝ)/8 by ring]
  ring
#print axioms program_semantics
#print axioms envelope_semantics
end WinnerDensityA.HeightProgram
