/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.HeightExpression
import PVEvolutionA.SlopedMoment
namespace PVEvolutionA.SlopedProgram
open WinnerDensityA
open Real LeanCert.Core LeanCert.Engine WinnerDensityA.Program WinnerDensityA.HeightExpression
open PVEvolutionA.SlopedMoment
set_option maxHeartbeats 0

def coeffExpr (j:Fin 4) (s:Expr) : Expr :=
  mul (lit (WinnerHeightProfiles.row j).K) (.exp (mul (lit (slope j)) (sub s (lit (7/8)))))
def correctionExpr (s : Expr) : Expr :=
  add (add (mul (sub (coeffExpr 0 s) (coeffExpr 1 s)) (lowerExpr s 1))
    (mul (sub (coeffExpr 1 s) (coeffExpr 2 s)) (lowerExpr s 2)))
      (mul (sub (coeffExpr 2 s) (coeffExpr 3 s)) (lowerExpr s 4))
def envelopeExpr (s : Expr) (τ : ℚ) : Expr :=
  sub (WinnerDensityA.ModelProgram.modelEnvelopeExpr (72931/10000) (54281/10000) 6 s τ)
    (mul (lit 2) (correctionExpr s))
noncomputable def correction (s : ℝ) :=
  (coeff 0 s-coeff 1 s)*lowerExp s (log WinnerDensityA.H+1)+
    (coeff 1 s-coeff 2 s)*lowerExp s (log WinnerDensityA.H+2)+
    (coeff 2 s-coeff 3 s)*lowerExp s (log WinnerDensityA.H+4)
noncomputable def mathEnvelope (s τ : ℝ) :=
  WinnerDensityA.envelope (WinnerDensityA.ModelProgram.modelC (72931/10000) (54281/10000) s) 6 s τ-
    2*correction s

theorem coeff_semantics (j:Fin 4) (s:Expr) (env:ℕ→ℝ) :
    Expr.eval env (coeffExpr j s)=coeff j (Expr.eval env s) := by
  simp only [coeffExpr,Expr.eval,lit,mul,sub,WinnerProgramA.sub,coeff]
  push_cast
  rfl

theorem correction_semantics (s : Expr) (env : ℕ→ℝ) :
    Expr.eval env (correctionExpr s)=correction (Expr.eval env s) := by
  simp only [correctionExpr,Expr.eval,lower_semantics,coeff_semantics,lit,add,mul,sub,WinnerProgramA.sub,correction]
  push_cast
  ring

theorem envelope_semantics (s : Expr) (τ : ℚ) (env : ℕ→ℝ) (hτ : 0<(τ:ℝ)) :
    Expr.eval env (envelopeExpr s τ)=mathEnvelope (Expr.eval env s) τ := by
  simp only [envelopeExpr,Expr.eval,WinnerDensityA.ModelProgram.model_envelope_semantics _ _ _ _ hτ,
    correction_semantics,lit,sub,mul,WinnerProgramA.sub,mathEnvelope]
  push_cast
  ring

def base (L τ : ℚ) : Expr :=
  add (mul (.exp (lit (-L/8))) (envelopeExpr (lit (3/4)) τ)) (Program.baseExpr 0 0 L τ)
theorem envelope_link (s τ:ℝ) : mathEnvelope s τ=PVEvolutionA.SlopedMoment.envelope s τ := by
  have h1:=lower_real s 1 (by norm_num)
  have h2:=lower_real s 2 (by norm_num)
  have h4:=lower_real s 4 (by norm_num)
  unfold mathEnvelope correction
  rw [h1,h2,h4]
  unfold WinnerDensityA.envelope WinnerDensityA.moment PVEvolutionA.SlopedMoment.envelope
    PVEvolutionA.SlopedMoment.moment PVEvolutionA.SlopedMoment.coeff
    PVEvolutionA.SlopedMoment.p PVEvolutionA.SlopedMoment.q
    WinnerDensityA.ModelProgram.modelC
  rw [←initial_upper]
  norm_num [WinnerHeightProfiles.row,WinnerHeightProfiles.anchor,
    WinnerOriginalScalars.height,WinnerDensityA.H,PVEvolutionA.SlopedMoment.slope] <;> push_cast <;> ring
#print axioms envelope_link
end PVEvolutionA.SlopedProgram
