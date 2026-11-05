/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OriginalSharpScalars
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
namespace WinnerEulerGamma
open Real LeanCert.Core WinnerOriginalScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def harmonicExpr : ℕ→Expr
  | 0 => lit 0
  | n+1 => add (harmonicExpr n) (lit (1/(n+1:ℚ)))

theorem harmonicExpr_semantics (n : ℕ) : value (harmonicExpr n)=(harmonic n:ℝ) := by
  induction n with
  | zero => simp [harmonicExpr,harmonic]
  | succ n ih =>
    simp [harmonicExpr,harmonic_succ,ih]

def upperExpr : Expr := sub (harmonicExpr 700) (.log (lit 700))

theorem upper_check : value upperExpr ≤ 289/500 := by
  have h := closed_upper upperExpr (289/500) (by native_decide)
  norm_num at h ⊢
  exact h

theorem euler_gamma_upper : eulerMascheroniConstant ≤ 289/500 := by
  have h := eulerMascheroniConstant_lt_eulerMascheroniSeq' 700
  have hv : value upperExpr=(harmonic 700:ℝ)-log 700 := by simp [upperExpr,harmonicExpr_semantics]
  have hc:=upper_check
  rw [hv] at hc
  norm_num only [eulerMascheroniSeq',show ¬(700:ℕ)=0 by decide,ite_false,Nat.cast_ofNat] at h
  exact h.le.trans hc

#print axioms euler_gamma_upper
end WinnerEulerGamma
