/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Graded
import PVEvolutionA.SlopedProgram
namespace PVEvolutionA.Sloped
open Real LeanCert.Core LeanCert.Engine WinnerDensityA WinnerDensityA.Program
set_option maxHeartbeats 0
def gradedTerm (L τ : ℚ) (n : ℕ) : Expr :=
  let s:=sigmaExpr n (.var 0)
  let r:=sigmaExpr n (add (.var 0) (lit 1))
  mul (sub (.exp (mul (lit L) (sub r (lit (7/8)))))
    (.exp (mul (lit L) (sub s (lit (7/8)))))) (SlopedProgram.envelopeExpr s τ)
def program (L τ : ℚ) (n : ℕ) : List WinnerProgramA.Row :=
  [⟨SlopedProgram.base L τ,1⟩,⟨gradedTerm L τ n,n⟩]
noncomputable def coefficient (n : ℕ) (L τ : ℝ) :=
  gridCoefficient (fun s=>SlopedProgram.mathEnvelope s τ) (gradedGrid n) n L+
    exp (-L/8)*((τ+1/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*(τ+1/10^9))+1/10^12

theorem program_semantics (L τ : ℚ) {n : ℕ} (hn : 0<n) (hτ : 0<(τ:ℝ)) :
    WinnerProgramA.value (program L τ n)=coefficient n L τ := by
  have hset : Finset.Icc 0 (n-1)=Finset.range n := by ext k;simp only [Finset.mem_Icc,Finset.mem_range];omega
  simp only [WinnerProgramA.value,program,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,WinnerProgramA.rowValue,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton,hset]
  have hbase : Expr.eval (sumBodyRealEnv 0) (SlopedProgram.base L τ)=
      exp (-(L:ℝ)/8)*SlopedProgram.mathEnvelope (3/4) τ+
      exp (-(L:ℝ)/8)*(((τ:ℝ)+1/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((τ:ℝ)+1/10^9))+1/10^12 := by
    simp only [SlopedProgram.base,Expr.eval,SlopedProgram.envelope_semantics _ _ _ hτ,Program.baseExpr,
      Program.envelope_semantics,lit,add,mul,sub,dv,pw,WinnerProgramA.sub,
      WinnerProgramA.divE,WinnerProgramA.powE,LeanCert.Core.MathConst.toReal]
    push_cast
    unfold Program.expEnvelope WinnerProgramA.momentReal
    dsimp only
    ring
  rw [hbase]
  unfold coefficient gridCoefficient
  have hterms : (∑ k∈Finset.range n,Expr.eval (sumBodyRealEnv k) (gradedTerm L τ n))=
      ∑ k∈Finset.range n,
        (exp ((L:ℝ)*(gradedGrid n (k+1)-7/8))-exp ((L:ℝ)*(gradedGrid n k-7/8)))*
          SlopedProgram.mathEnvelope (gradedGrid n k) τ := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k<n := Finset.mem_range.mp hk
    have hkn : k≤n := hk'.le
    have hks : k+1≤n := hk'
    simp only [gradedTerm,Expr.eval,SlopedProgram.envelope_semantics _ _ _ hτ,
      sigmaExpr,sumBodyRealEnv,lit,add,mul,sub,dv,pw,WinnerProgramA.sub,WinnerProgramA.divE,WinnerProgramA.powE]
    unfold gradedGrid
    rw [Nat.cast_sub hkn,Nat.cast_sub hks]
    push_cast
    congr 2 <;> congr 1 <;> ring
  rw [hterms,graded_zero hn]
  rw [show (L:ℝ)*((3/4:ℝ)-7/8)=-(L:ℝ)/8 by ring]
  ring
#print axioms program_semantics
end PVEvolutionA.Sloped
