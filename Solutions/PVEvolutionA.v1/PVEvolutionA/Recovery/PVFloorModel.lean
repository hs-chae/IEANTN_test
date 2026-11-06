/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- Lower certificate for the entire frozen PV allowance, not for the actual error. -/
import PVEvolutionA.Recovery.BoxLower
import PVEvolutionA.SlopedGraded
namespace PVEvolutionA.Recovery.PVFloor
open Real LeanCert.Core LeanCert.Engine WinnerDensityA WinnerDensityA.Program
set_option maxHeartbeats 0

def cells : Nat := 4096

def sigmaQ (n i : Nat) : ℚ := 7/8-((n-i:Nat):ℚ)^3/(8*(n:ℚ)^3)
theorem sigmaQ_cast (n i : Nat) : (sigmaQ n i : ℝ)=gradedGrid n i := by
  unfold sigmaQ gradedGrid
  push_cast
  ring

def box (i : Nat) : IntervalRat :=
  ⟨sigmaQ cells i, sigmaQ cells (i+1), by
    apply Rat.cast_le (K:=ℝ) |>.mp
    simpa only [sigmaQ_cast] using graded_monotone cells (Nat.le_succ i)⟩

def momentExpr : Expr :=
  mul (lit 2) (sub
    (add (mul (SlopedProgram.coeffExpr 0 (.var 0)) (WinnerProgramA.moment (.var 0) 1 0))
      (WinnerProgramA.moment (.var 0) 0 6))
    (SlopedProgram.correctionExpr (.var 0)))
noncomputable def momentOnly (s : ℝ) : ℝ :=
  2*(WinnerProgramA.momentReal s (SlopedMoment.coeff 0 s) 6-SlopedProgram.correction s)

theorem moment_semantics (env : Nat→ℝ) : Expr.eval env momentExpr=momentOnly (env 0) := by
  simp only [momentExpr, Expr.eval, lit,mul,add,sub,WinnerProgramA.sub,
    SlopedProgram.coeff_semantics, WinnerProgramA.moment_semantics,
    SlopedProgram.correction_semantics]
  norm_num only [Rat.cast_ofNat]
  unfold momentOnly WinnerProgramA.momentReal
  ring

theorem moment_le_envelope (s τ : ℝ) (hτ : 0<τ) :
    momentOnly s≤SlopedProgram.mathEnvelope s τ := by
  have hpos := SlopedMoment.coeff_nonneg 0 s
  have hc : WinnerDensityA.ModelProgram.modelC (72931/10000) (54281/10000) s=
      SlopedMoment.coeff 0 s := by
    norm_num [WinnerDensityA.ModelProgram.modelC, SlopedMoment.coeff,
      WinnerHeightProfiles.row,SlopedMoment.slope]
  unfold SlopedProgram.mathEnvelope
  rw [hc, ←Program.envelope_real _ _ _ _ hτ]
  unfold Program.expEnvelope momentOnly
  have htail : 0≤4*Real.pi*(SlopedMoment.coeff 0 s *
      exp (-((8*s-5)/3)*τ+(5-2*s)*log τ)+6*τ^2*exp (-τ)) := by positivity
  linarith

/-- Actual evaluator-produced lower endpoint; no external table is trusted. -/
def cap (i : Nat) : ℚ :=
  (BoxLower.output momentExpr (box (min i (cells-1)))).1.lo.toRat
end PVEvolutionA.Recovery.PVFloor
