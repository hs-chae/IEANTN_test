/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Comparison
import PVEvolutionA.PointwiseConsumer
namespace PVEvolutionA
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0
/-- Exact, generally real-parameter finite majorant. This is an analytic
expression, not a claim of executing an irrational input as a rational AST. -/
noncomputable def pointCoefficient (x:ℝ) : ℝ :=
  (1+33/10000000000000000)*Sloped.coefficient 65536 (log x) (log x/3)+
    1/10000000000000000000000000000+1/10000000000000
noncomputable def pointBound (x:ℝ) : ℝ := pointCoefficient x*scale x
/-- Keep every certified cap and the exact pointwise analytic majorant. -/
noncomputable def bestBound (x:ℝ) : ℝ := min (bound x) (pointBound x)

section OriginalInputs
variable
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
include hCHJ hrvm hsmall hlow h hRH hQRH
/-- This pointwise finite-sum theorem alone uses no new outer-grid execution
fact. The numerical constants in Result require their concrete certificates. -/
theorem pi_pointwise {x:ℝ} (hx:exp (300:ℝ) ≤ x) : Eπ x ≤ pointBound x := by
  have hp : 0<x := (exp_pos _).trans_le hx
  have hL : 300 ≤ log x := by simpa only [log_exp] using log_le_log (exp_pos _) hx
  have hh:=PointwiseConsumer.pi_from_graded_coefficient hCHJ hrvm hsmall hlow h hRH hQRH
    (by decide : 0<(65536:ℕ)) hL (le_rfl : Sloped.coefficient 65536 (log x) (log x/3) ≤ Sloped.coefficient 65536 (log x) (log x/3)) x (by rw [exp_log hp])
  simpa only [pointBound,pointCoefficient,scale,pow_zero,mul_one,
    show (7/8:ℝ)-1= -(1:ℝ)/8 by norm_num] using hh
/-- An actual certificate-dependent whole-ray bound retaining the unrounded
analytic function. Stronger future no-PV results can be added by another min. -/
theorem pi_best {x:ℝ} (hx:exp (300:ℝ) ≤ x) : Eπ x ≤ bestBound x :=
  le_min (pi_evolved hCHJ hrvm hsmall hlow h hRH hQRH hx)
    (pi_pointwise hCHJ hrvm hsmall hlow h hRH hQRH hx)

theorem best_snapshot_evolution {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x) :
    Eπ x ≤ bestBound x ∧ Eπ x ≤ scopedExact*scale x ∧
    Eπ x ≤ ScopedWinnerA.Coverage.envelope x ∧
    bestBound x+(32094/100000000:ℝ)*scale x<scopedExact*scale x ∧
    bestBound x+(32393/100000000:ℝ)*scale x<ScopedWinnerA.Coverage.envelope x := by
  have hj:=snapshot_evolution hCHJ hrvm hsmall hlow h hRH hQRH hx
  have hb:=min_le_left (bound x) (pointBound x)
  exact ⟨pi_best hCHJ hrvm hsmall hlow h hRH hQRH
    ((exp_le_exp.mpr (by norm_num : (300:ℝ) ≤ 330)).trans hx.1),hj.2.1,hj.2.2.1,
    (add_le_add hb le_rfl).trans_lt hj.2.2.2.1,
    (add_le_add hb le_rfl).trans_lt hj.2.2.2.2.1⟩
end OriginalInputs
#print axioms pi_pointwise
#print axioms pi_best
#print axioms best_snapshot_evolution
end PVEvolutionA
