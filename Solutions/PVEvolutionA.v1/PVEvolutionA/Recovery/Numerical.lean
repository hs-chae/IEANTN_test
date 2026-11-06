/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.ManyMomentModel
import PVEvolutionA.Graded
import WinnerDensityA.HeightExpression

namespace PVEvolutionA.Recovery.Numerical
open Real LeanCert.Core LeanCert.Engine WinnerDensityA WinnerDensityA.Program
open WinnerDensityA.HeightExpression
set_option maxHeartbeats 0

def coeffExpr (j : ℕ) (s : Expr) : Expr :=
  mul (lit (Profiles.row (Profiles.index j)).K)
    (.exp (mul (lit (Profiles.slope (Profiles.index j))) (sub s (lit (7/8)))))

def correctionTerm (j : ℕ) (s : Expr) : Expr :=
  mul (sub (coeffExpr j s) (coeffExpr (j+1) s))
    (lowerExpr s (Profiles.row (Profiles.index (j+1))).shift)

def correctionAux (s : Expr) : ℕ→Expr
  | 0 => lit 0
  | n+1 => add (correctionAux s n) (correctionTerm n s)

def envelopeExpr (s : Expr) (tau : ℚ) : Expr :=
  sub (WinnerDensityA.ModelProgram.modelEnvelopeExpr
    (Profiles.row (Profiles.index 0)).K (Profiles.slope (Profiles.index 0)) 6 s tau)
    (mul (lit 2) (correctionAux s 127))

theorem coeff_semantics (j : ℕ) (s : Expr) (env : ℕ→ℝ) :
    Expr.eval env (coeffExpr j s)=Profiles.coeff (Expr.eval env s) j := by
  simp only [coeffExpr,Expr.eval,lit,mul,sub,WinnerProgramA.sub,Profiles.coeff]
  push_cast
  rfl

theorem correction_semantics (s : Expr) (env : ℕ→ℝ) (n : ℕ) :
    Expr.eval env (correctionAux s n)=
      ∑j∈Finset.range n,(Profiles.coeff (Expr.eval env s) j-Profiles.coeff (Expr.eval env s) (j+1))*
        Piecewise.lower (Model.p (Expr.eval env s)) (Model.q (Expr.eval env s)) (Profiles.anchor (j+1)) := by
  induction n with
  | zero => simp [correctionAux,lit,Expr.eval]
  | succ n ih =>
    have hshift : (0:ℝ)≤(Profiles.row (Profiles.index (n+1))).shift := by
      exact_mod_cast (Profiles.arithmetic (Profiles.index (n+1))).1
    have hl := lower_real (Expr.eval env s) ((Profiles.row (Profiles.index (n+1))).shift:ℝ) hshift
    simp only [correctionAux,Expr.eval,ih,Finset.sum_range_succ,correctionTerm,
      coeff_semantics,lower_semantics,mul,sub,WinnerProgramA.sub,add]
    rw [hl]
    norm_num only [Model.p,Model.q,Profiles.anchor,Profile.anchor,WinnerOriginalScalars.height,H]
    ring

theorem envelope_semantics (s : Expr) (tau : ℚ) (env : ℕ→ℝ) (ht : 0<(tau:ℝ)) :
    Expr.eval env (envelopeExpr s tau)=Model.envelope (Expr.eval env s) tau := by
  have he : WinnerDensityA.ModelProgram.modelC (Profiles.row (Profiles.index 0)).K
      (Profiles.slope (Profiles.index 0)) (Expr.eval env s)=Profiles.coeff (Expr.eval env s) 0 := by
    unfold WinnerDensityA.ModelProgram.modelC Profiles.coeff
    congr 1 <;> ring
  simp only [envelopeExpr,Expr.eval,
    WinnerDensityA.ModelProgram.model_envelope_semantics _ _ _ _ ht,
    correction_semantics,lit,mul,sub,WinnerProgramA.sub]
  rw [he]
  unfold Model.envelope Model.moment ManyStep.budget Model.p Model.q
    WinnerDensityA.envelope WinnerDensityA.moment
  rw [←initial_upper]
  ring

def base (L tau : ℚ) : Expr :=
  add (mul (.exp (lit (-L/8))) (envelopeExpr (lit (3/4)) tau))
    (Program.baseExpr 0 0 L (L/3))

def gradedTerm (L tau : ℚ) (n : ℕ) : Expr :=
  let s:=PVEvolutionA.sigmaExpr n (.var 0)
  let r:=PVEvolutionA.sigmaExpr n (add (.var 0) (lit 1))
  mul (sub (.exp (mul (lit L) (sub r (lit (7/8)))))
    (.exp (mul (lit L) (sub s (lit (7/8)))))) (envelopeExpr s tau)

def program (L tau : ℚ) (n : ℕ) : List WinnerProgramA.Row :=
  [⟨base L tau,1⟩,⟨gradedTerm L tau n,n⟩]

noncomputable def coefficient (n : ℕ) (L tau : ℝ) : ℝ :=
  gridCoefficient (fun s=>Model.envelope s tau) (PVEvolutionA.gradedGrid n) n L+
    exp (-L/8)*((L/3+1/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*(L/3+1/10^9))+1/10^12

theorem program_semantics (L τ : ℚ) {n : ℕ} (hn : 0<n) (hτ : 0<(τ:ℝ)) :
    WinnerProgramA.value (program L τ n)=coefficient n L τ := by
  have hset : Finset.Icc 0 (n-1)=Finset.range n := by ext k;simp only [Finset.mem_Icc,Finset.mem_range];omega
  simp only [WinnerProgramA.value,program,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,WinnerProgramA.rowValue,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton,hset]
  have hbase : Expr.eval (sumBodyRealEnv 0) (base L τ)=
      exp (-(L:ℝ)/8)*Model.envelope (3/4) τ+
      exp (-(L:ℝ)/8)*((((L:ℝ)/3)+1/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*(((L:ℝ)/3)+1/10^9))+1/10^12 := by
    simp only [base,Expr.eval,envelope_semantics _ _ _ hτ,Program.baseExpr,
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
          Model.envelope (gradedGrid n k) τ := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k<n := Finset.mem_range.mp hk
    have hkn : k≤n := hk'.le
    have hks : k+1≤n := hk'
    simp only [gradedTerm,Expr.eval,envelope_semantics _ _ _ hτ,
      sigmaExpr,sumBodyRealEnv,lit,add,mul,sub,dv,pw,WinnerProgramA.sub,WinnerProgramA.divE,WinnerProgramA.powE]
    unfold gradedGrid
    rw [Nat.cast_sub hkn,Nat.cast_sub hks]
    push_cast
    congr 2 <;> congr 1 <;> ring
  rw [hterms,graded_zero hn]
  rw [show (L:ℝ)*((3/4:ℝ)-7/8)=-(L:ℝ)/8 by ring]
  ring

#print axioms program_semantics
#print axioms correction_semantics
#print axioms envelope_semantics
end PVEvolutionA.Recovery.Numerical
