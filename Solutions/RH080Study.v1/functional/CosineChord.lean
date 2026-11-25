/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

set_option autoImplicit false
open Real Set
namespace RH080.Dual

lemma convex_quadratic_add_cos :
    ConvexOn ℝ univ (fun x : ℝ => x ^ 2 / 2 + cos x) := by
  have hd : deriv (fun x : ℝ => x ^ 2 / 2 + cos x) = fun x => x - sin x := by
    funext x
    have h := ((((hasDerivAt_id x).pow 2).div_const 2).add (hasDerivAt_cos x)).deriv
    convert h using 1 <;> first | rfl | (simp <;> ring)
  apply convexOn_univ_of_deriv2_nonneg
  · fun_prop
  · rw [hd]
    fun_prop
  · intro x
    change 0 ≤ deriv (deriv (fun x : ℝ => x ^ 2 / 2 + cos x)) x
    rw [hd]
    have hx := ((hasDerivAt_id x).sub (hasDerivAt_sin x)).deriv
    change 0 ≤ deriv (id - sin) x
    rw [hx]
    linarith [cos_le_one x]

lemma convex_quadratic_sub_cos :
    ConvexOn ℝ univ (fun x : ℝ => x ^ 2 / 2 - cos x) := by
  have hd : deriv (fun x : ℝ => x ^ 2 / 2 - cos x) = fun x => x + sin x := by
    funext x
    have h := ((((hasDerivAt_id x).pow 2).div_const 2).sub (hasDerivAt_cos x)).deriv
    convert h using 1 <;> first | rfl | (simp <;> ring)
  apply convexOn_univ_of_deriv2_nonneg
  · fun_prop
  · rw [hd]
    fun_prop
  · intro x
    change 0 ≤ deriv (deriv (fun x : ℝ => x ^ 2 / 2 - cos x)) x
    rw [hd]
    have hx := ((hasDerivAt_id x).add (hasDerivAt_sin x)).deriv
    change 0 ≤ deriv (id + sin) x
    rw [hx]
    linarith [neg_one_le_cos x]

/-- Full real cosine chord error, obtained from convexity of x²/2±cos x.
No finite sampling or numerical oracle occurs in this continuum theorem. -/
theorem cosine_chord_error (a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |cos ((1 - t) * a + t * b) - ((1 - t) * cos a + t * cos b)| ≤
      (b - a) ^ 2 / 8 := by
  have hp := (convex_quadratic_add_cos.2)
    (mem_univ a) (mem_univ b)
    (show 0 ≤ 1-t by linarith) ht0 (show (1-t)+t=1 by ring)
  have hm := (convex_quadratic_sub_cos.2)
    (mem_univ a) (mem_univ b)
    (show 0 ≤ 1-t by linarith) ht0 (show (1-t)+t=1 by ring)
  simp only [smul_eq_mul] at hp hm
  have hs : 0 ≤ (t - 1/2) ^ 2 := sq_nonneg _
  have hab : 0 ≤ (b-a)^2 := sq_nonneg _
  have hedge : t*(1-t) ≤ (1/4 : ℝ) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hedge hab
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The same interpolation bound for a cosine frequency v on a real cell. -/
theorem scaled_cosine_chord_error (a b t v : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |cos (2*π*v*((1-t)*a+t*b)) -
      ((1-t)*cos (2*π*v*a)+t*cos (2*π*v*b))| ≤
      π^2*v^2*(b-a)^2/2 := by
  have h := cosine_chord_error (2*π*v*a) (2*π*v*b) t ht0 ht1
  rw [show (1-t)*(2*π*v*a)+t*(2*π*v*b) = 2*π*v*((1-t)*a+t*b) by ring] at h
  calc
    _ ≤ (2*π*v*b-2*π*v*a)^2/8 := h
    _ = _ := by ring

#print axioms cosine_chord_error
end RH080.Dual
