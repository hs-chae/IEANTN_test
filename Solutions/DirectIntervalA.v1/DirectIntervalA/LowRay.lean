/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.Common
import WinnerProgramA.Program

open Real Set MeasureTheory

namespace DirectIntervalA

noncomputable def lowLog (L : ℝ) : ℝ := L / 5 + log (240 * L)

theorem low_eq_explicit {L : ℝ} (hL : 330 ≤ L) :
    low L = 2 * k * exp (-L / 20) * (lowLog L + lowLog L ^ (2 : ℕ) / 2) := by
  have hLpos : 0 < L := by linarith
  have hV : V L = (240 * L) * exp (L / 5) := by unfold V truncHeight; ring
  unfold low lowLog
  rw [hV, Real.log_mul (by positivity) (exp_pos _).ne', Real.log_exp]
  ring

theorem lowLog_deriv {L : ℝ} (hL : 0 < L) :
    HasDerivAt lowLog (1 / 5 + 1 / L) L := by
  have hd₁ := (hasDerivAt_id L).div_const (5 : ℝ)
  have hd₂ := ((hasDerivAt_id L).const_mul (240 : ℝ)).log (by positivity)
  convert! hd₁.add hd₂ using 1 <;> dsimp [lowLog]
  all_goals field_simp
  all_goals ring

/-- The elementary low-real-part contribution decreases on the entire real ray. -/
theorem low_antitoneOn : AntitoneOn low (Ici (330 : ℝ)) := by
  let f : ℝ → ℝ := fun L ↦
    2 * k * exp (-L / 20) * (lowLog L + lowLog L ^ (2 : ℕ) / 2)
  let d : ℝ → ℝ := fun L ↦ 2 * k * exp (-L / 20) *
    ((1 / 5 + 1 / L) * (1 + lowLog L) -
      (lowLog L + lowLog L ^ (2 : ℕ) / 2) / 20)
  have hder : ∀ L ∈ Ici (330 : ℝ), HasDerivAt f (d L) L := by
    intro L hL
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
    have hv := lowLog_deriv hLpos
    have he := (((hasDerivAt_id L).neg).div_const (20 : ℝ)).exp
    have hp := hv.add ((hv.pow 2).div_const (2 : ℝ))
    have hd := (he.mul hp).const_mul (2 * k)
    convert! hd using 1 <;> dsimp [f, d] <;> ring
  have hanti : AntitoneOn f (Ici (330 : ℝ)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (330 : ℝ))
      (fun L hL ↦ (hder L hL).continuousAt.continuousWithinAt)
      (fun L hL ↦ (hder L (interior_subset hL)).hasDerivWithinAt)
    intro L hL
    have hLL : (330 : ℝ) ≤ L := interior_subset hL
    have hLpos : 0 < L := by linarith
    have hlog : 0 ≤ log (240 * L) := Real.log_nonneg (by nlinarith)
    have hv : (66 : ℝ) ≤ lowLog L := by unfold lowLog; linarith
    have hInv : (1 : ℝ) / L ≤ 1 := (div_le_one hLpos).mpr (by linarith)
    have hdv : (1 / 5 : ℝ) + 1 / L ≤ 1 := by
      have hInv' : (1 : ℝ) / L ≤ 1 / 2 := by
        apply (div_le_iff₀ hLpos).mpr
        linarith
      linarith
    have hm : (1 / 5 + 1 / L) * (1 + lowLog L) ≤ 1 + lowLog L := by
      nlinarith [mul_le_mul_of_nonneg_right hdv (show 0 ≤ 1 + lowLog L by linarith)]
    have hs : (1 / 5 + 1 / L) * (1 + lowLog L) -
        (lowLog L + lowLog L ^ (2 : ℕ) / 2) / 20 ≤ 0 := by
      nlinarith [mul_nonneg (show 0 ≤ lowLog L - 66 by linarith)
        (show 0 ≤ lowLog L by linarith)]
    exact mul_nonpos_of_nonneg_of_nonpos (by dsimp [k]; positivity) hs
  intro L hL M hM hLM
  rw [low_eq_explicit hM, low_eq_explicit hL]
  exact hanti hL hM hLM

namespace LowNumerical
open LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def logExpr : Expr := add (lit 66) (.log (lit 79200))
def lowExpr : Expr := mul (lit (201 / 50))
  (mul (.exp (lit (-33 / 2))) (add logExpr (divE (powE logExpr 2) (lit 2))))
def row : Row := ⟨lowExpr, 1⟩
def program : List Row := [row]
def output : IntervalDyadic × Bool := runRow row

theorem execution : Exec program [output] := rfl

theorem semantics : value program = low 330 := by
  simp only [value, program, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    rowValue, row, Nat.sub_self, Finset.Icc_self, Finset.sum_singleton]
  rw [low_eq_explicit (by norm_num : (330 : ℝ) ≤ 330)]
  norm_num [lowExpr, logExpr, Expr.eval, lit, add, mul, WinnerProgramA.divE, powE, lowLog, k]
  ring

/-- One closed execution/domain certificate for the actual selected source row. -/
theorem checked : acceptUpper [output] [(1 / 1000 : ℚ)] = true := by
  native_decide

theorem low330_le : low 330 ≤ (1 / 1000 : ℝ) := by
  have hb := source_linked_upper program [output] [(1 / 1000 : ℚ)] execution checked
  rw [semantics] at hb
  norm_num at hb ⊢
  exact hb

/-- A cap below the actual low contribution is rejected by that same execution. -/
theorem rejects_small_cap : acceptUpper [output] [(8 / 10000 : ℚ)] = false := by
  native_decide

end LowNumerical

theorem low_le {L : ℝ} (hL : 330 ≤ L) : low L ≤ (1 / 1000 : ℝ) :=
  (low_antitoneOn (show (330 : ℝ) ∈ Ici 330 by simp) hL hL).trans LowNumerical.low330_le

end DirectIntervalA

#print axioms DirectIntervalA.low_antitoneOn
#print axioms DirectIntervalA.LowNumerical.low330_le
#print axioms DirectIntervalA.low_le
