/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.HeightProgram
namespace PVEvolutionA
open Real LeanCert.Core LeanCert.Engine WinnerDensityA WinnerDensityA.Program
set_option maxHeartbeats 0
/-- A cubic partition clusters cells near the QRH boundary. Truncation makes
this a monotone sequence on every natural index, including indices beyond n. -/
noncomputable def gradedGrid (n i : ℕ) : ℝ :=
  7/8-(((n-i:ℕ):ℝ)/(n:ℝ))^3/8

theorem graded_monotone (n : ℕ) : Monotone (gradedGrid n) := by
  intro i j hij
  have hsub : ((n-j:ℕ):ℝ) ≤ ((n-i:ℕ):ℝ) := by exact_mod_cast Nat.sub_le_sub_left hij n
  have hr : 0 ≤ ((n-j:ℕ):ℝ)/(n:ℝ) := by positivity
  have hh : ((n-j:ℕ):ℝ)/(n:ℝ) ≤ ((n-i:ℕ):ℝ)/(n:ℝ) :=
    div_le_div_of_nonneg_right hsub (Nat.cast_nonneg n)
  have hp : (((n-j:ℕ):ℝ)/(n:ℝ))^3 ≤ (((n-i:ℕ):ℝ)/(n:ℝ))^3 := by gcongr
  unfold gradedGrid
  linarith

theorem graded_zero {n : ℕ} (hn : 0<n) : gradedGrid n 0=(3/4:ℝ) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  norm_num [gradedGrid,hn0]
theorem graded_last (n : ℕ) : gradedGrid n n=(7/8:ℝ) := by simp [gradedGrid]

def sigmaExpr (n : ℕ) (v : Expr) : Expr :=
  sub (lit (7/8)) (dv (pw (dv (sub (lit n) v) (lit n)) 3) (lit 8))
def gradedTerm (L τ : ℚ) (n : ℕ) : Expr :=
  let s:=sigmaExpr n (.var 0)
  let r:=sigmaExpr n (add (.var 0) (lit 1))
  mul (sub (.exp (mul (lit L) (sub r (lit (7/8)))))
    (.exp (mul (lit L) (sub s (lit (7/8)))))) (HeightProgram.envelopeExpr s τ)
def gradedProgram (L τ : ℚ) (n : ℕ) : List WinnerProgramA.Row :=
  [⟨HeightProgram.base L τ,1⟩,⟨gradedTerm L τ n,n⟩]
noncomputable def gradedCoefficient (n : ℕ) (L τ : ℝ) :=
  gridCoefficient (fun s=>HeightProgram.mathEnvelope s τ) (gradedGrid n) n L+
    exp (-L/8)*((τ+1/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*(τ+1/10^9))+1/10^12

theorem sigma_semantics {n i : ℕ} (hi : i≤n) :
    Expr.eval (sumBodyRealEnv i) (sigmaExpr n (.var 0))=gradedGrid n i := by
  simp only [sigmaExpr,Expr.eval,lit,sub,dv,pw,WinnerProgramA.sub,WinnerProgramA.divE,
    WinnerProgramA.powE,sumBodyRealEnv]
  unfold gradedGrid
  rw [Nat.cast_sub hi]
  push_cast
  ring

theorem graded_program_semantics (L τ : ℚ) {n : ℕ} (hn : 0<n) (hτ : 0<(τ:ℝ)) :
    WinnerProgramA.value (gradedProgram L τ n)=gradedCoefficient n L τ := by
  have hset : Finset.Icc 0 (n-1)=Finset.range n := by ext k;simp only [Finset.mem_Icc,Finset.mem_range];omega
  simp only [WinnerProgramA.value,gradedProgram,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,WinnerProgramA.rowValue,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton,hset]
  have hbase : Expr.eval (sumBodyRealEnv 0) (HeightProgram.base L τ)=
      exp (-(L:ℝ)/8)*HeightProgram.mathEnvelope (3/4) τ+
      exp (-(L:ℝ)/8)*(((τ:ℝ)+1/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((τ:ℝ)+1/10^9))+1/10^12 := by
    simp only [HeightProgram.base,Expr.eval,HeightProgram.envelope_semantics _ _ _ hτ,Program.baseExpr,
      Program.envelope_semantics,lit,add,mul,sub,dv,pw,WinnerProgramA.sub,
      WinnerProgramA.divE,WinnerProgramA.powE,LeanCert.Core.MathConst.toReal]
    push_cast
    unfold Program.expEnvelope WinnerProgramA.momentReal
    dsimp only
    ring
  rw [hbase]
  unfold gradedCoefficient gridCoefficient
  have hterms : (∑ k∈Finset.range n,Expr.eval (sumBodyRealEnv k) (gradedTerm L τ n))=
      ∑ k∈Finset.range n,
        (exp ((L:ℝ)*(gradedGrid n (k+1)-7/8))-exp ((L:ℝ)*(gradedGrid n k-7/8)))*
          HeightProgram.mathEnvelope (gradedGrid n k) τ := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k<n := Finset.mem_range.mp hk
    have hkn : k≤n := hk'.le
    have hks : k+1≤n := hk'
    simp only [gradedTerm,Expr.eval,HeightProgram.envelope_semantics _ _ _ hτ,
      sigmaExpr,sumBodyRealEnv,lit,add,mul,sub,dv,pw,WinnerProgramA.sub,WinnerProgramA.divE,WinnerProgramA.powE]
    unfold gradedGrid
    rw [Nat.cast_sub hkn,Nat.cast_sub hks]
    push_cast
    congr 2 <;> congr 1 <;> ring
  rw [hterms,graded_zero hn]
  rw [show (L:ℝ)*((3/4:ℝ)-7/8)=-(L:ℝ)/8 by ring]
  ring
#print axioms graded_program_semantics
end PVEvolutionA
