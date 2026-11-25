/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SineRational
import LeanCert.Core.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RH080.SineBridge
open Real

noncomputable def poly (x : ℝ) : ℝ :=
  x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 - x^11/39916800 +
  x^13/6227020800 - x^15/1307674368000 + x^17/355687428096000

lemma cast_polyQ (x : ℚ) : (polyQ x : ℝ) = poly (x : ℝ) := by
  norm_num [polyQ, poly]

lemma sin_taylor18 (x : ℝ) :
    (∑ i ∈ Finset.range 18, (iteratedDeriv i sin 0 / i.factorial) * x^i) = poly x := by
  norm_num [Finset.sum_range_succ, iteratedDeriv_succ', Real.deriv_sin,
    Real.deriv_cos', iteratedDeriv_fun_neg, poly]
  <;> ring

theorem sin_poly_error {x : ℝ} (hx : 0 ≤ x) (hupper : x ≤ 1571/1000) :
    |sin x - poly x| ≤ 1/1000000000000 := by
  have hb := LeanCert.Core.taylor_remainder_bound
    (a := (0 : ℝ)) (b := 1571/1000) (c := 0) (n := 18) (M := 1)
    (by norm_num) le_rfl (by norm_num) Real.contDiff_sin
    (fun y _ => by simpa [Real.norm_eq_abs] using Real.abs_iteratedDeriv_sin_le_one 18 y)
    (by norm_num) x ⟨hx,hupper⟩
  rw [sin_taylor18] at hb
  simp only [sub_zero, one_mul, Real.norm_eq_abs, abs_of_nonneg hx] at hb
  have hp : x^18 ≤ (1571/1000 : ℝ)^18 := pow_le_pow_left₀ hx hupper 18
  calc
    |sin x - poly x| ≤ x^18 / (18:ℕ).factorial := hb
    _ ≤ (1571/1000 : ℝ)^18 / (18:ℕ).factorial := div_le_div_of_nonneg_right hp (by positivity)
    _ ≤ 1/1000000000000 := by norm_num

theorem angle_reduction_error (r : Fin 129) :
    |((3141592654*r.val/256 : Nat) : ℝ)/1000000000 - π*r.val/256| ≤ 2/1000000000 := by
  have hnonneg : 0 ≤ (r.val : ℝ) := by positivity
  have hr : (r.val : ℝ) ≤ 128 := by exact_mod_cast (show r.val ≤ 128 by omega)
  have hmod : ((3141592654*r.val % 256 : Nat) : ℝ) ≤ 255 := by
    exact_mod_cast (show 3141592654*r.val % 256 ≤ 255 by omega)
  have hmod0 : (0 : ℝ) ≤ (3141592654*r.val % 256 : Nat) := by positivity
  have hid : (3141592654 : ℝ)*r.val =
      (3141592654*r.val % 256 : Nat) + 256*(3141592654*r.val/256 : Nat) := by
    exact_mod_cast (Nat.mod_add_div (3141592654*r.val) 256).symm
  have hlo := mul_le_mul_of_nonneg_right (le_of_lt pi_gt_d20) hnonneg
  have hhi := mul_le_mul_of_nonneg_right (le_of_lt pi_lt_d20) hnonneg
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A real sine enclosure for every actually supported fixed-point argument.
The rational rounding, true pi, Taylor remainder and all 129 finite cases are
proved separately. This theorem does not by itself assert C-source execution. -/
theorem sine_fixed_real_error (r : Fin 129) :
    |(sineFixed r.val : ℝ)/1000000000 - sin (π*r.val/256)| ≤ 1/10000000 := by
  let z : ℝ := ((3141592654*r.val/256 : Nat) : ℝ)/1000000000
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hr : r.val ≤ 128 := by omega
  have hdiv : 3141592654*r.val/256 ≤ 1571000000 := by omega
  have hzmax : z ≤ 1571/1000 := by
    have hc : ((3141592654*r.val/256 : Nat) : ℝ) ≤ 1571000000 := by exact_mod_cast hdiv
    dsimp [z]; linarith
  have hq := rational_error r
  have hc : ((|(sineFixed r.val : ℚ)/1000000000 -
      polyQ ((3141592654*r.val/256 : Nat)/1000000000 : ℚ)| : ℚ) : ℝ) ≤
      ((1/50000000 : ℚ) : ℝ) := by exact_mod_cast hq
  push_cast at hc
  rw [cast_polyQ] at hc
  have hround : |(sineFixed r.val : ℝ)/1000000000 - poly z| ≤ 1/50000000 := by
    simpa [z] using hc
  have ht := sin_poly_error hz hzmax
  have ha := angle_reduction_error r
  have hl := abs_sin_sub_sin_le z (π*r.val/256)
  have htri := abs_sub_le ((sineFixed r.val : ℝ)/1000000000) (poly z) (sin (π*r.val/256))
  have htri2 := abs_sub_le (poly z) (sin z) (sin (π*r.val/256))
  rw [abs_sub_comm (poly z) (sin z)] at htri2
  change |z - π*r.val/256| ≤ 2/1000000000 at ha
  linarith

end RH080.SineBridge

#print axioms RH080.SineBridge.sin_poly_error
#print axioms RH080.SineBridge.sine_fixed_real_error
