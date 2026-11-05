/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ReversKernelMath
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds

namespace WinnerReversDensity
open Real Set MeasureTheory
set_option maxHeartbeats 0

theorem kernel_nonneg (sign y : ℝ) : 0 ≤ kernelReal sign y := by
  unfold kernelReal
  positivity

theorem low_pointwise (y : ℝ) (hy : y ≤ -20) : kernelReal (-1) y ≤ 4*exp y := by
  have hy0 : y ≤ 0 := by linarith
  have hey : exp y ≤ 1 := exp_le_one_iff.mpr hy0
  have he6 : exp (y/6) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have he2 : exp (y/2) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hf : 0 ≤ 1+(-1:ℝ)*y/28 := by linarith
  have hs : sqrt ((129/200:ℝ)*exp y+23/250) ≤ 1 := by
    apply (sqrt_le_left (by norm_num : (0:ℝ)≤1)).2
    nlinarith
  let A := sqrt ((129/200:ℝ)*exp y+23/250)*
      (exp (y/6)*(1+(-1:ℝ)*y/28)+137/100000)+(47/500000)*exp (y/2)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA : A ≤ -y := by
    calc
      A ≤ 1*(1*(1+(-1:ℝ)*y/28)+137/100000)+(47/500000)*1 := by
        dsimp [A]
        gcongr
      _ ≤ -y := by linarith
  have hsquare : A^2 ≤ y^2 := by nlinarith
  have hweight : exp (2*y-(601/2500)*exp (2*y)) ≤ exp (2*y) := by
    apply exp_le_exp.mpr
    nlinarith [exp_pos (2*y)]
  have hfirst : kernelReal (-1) y ≤ exp (2*y)*y^2 := by
    dsimp [kernelReal]
    change exp (2*y-(601/2500)*exp (2*y))*A^2 ≤ _
    exact mul_le_mul hweight hsquare (sq_nonneg _) (exp_pos _).le
  have hexpsq : exp ((-y)/2)^2=exp (-y) := by
    rw [pow_two,←exp_add]
    congr 1
    ring
  have hlin := add_one_le_exp ((-y)/2)
  have hsq : ((-y)/2)^2 ≤ exp ((-y)/2)^2 := by
    gcongr <;> linarith
  rw [hexpsq] at hsq
  have hysq : y^2 ≤ 4*exp (-y) := by nlinarith
  calc
    kernelReal (-1) y ≤ exp (2*y)*y^2 := hfirst
    _ ≤ exp (2*y)*(4*exp (-y)) := by gcongr
    _ = 4*exp y := by rw [show exp (2*y)*(4*exp (-y))=4*(exp (2*y)*exp (-y)) by ring,←exp_add]; congr 2; ring

theorem exp_six_lower : (200:ℝ) ≤ exp 6 := by
  have he : (5/2:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have hp : (5/2:ℝ)^6 ≤ (exp 1)^6 := by gcongr
  have hpow : exp 6 = (exp 1)^6 := by
    simpa using (exp_nat_mul (1:ℝ) 6)
  rw [←hpow] at hp
  norm_num at hp ⊢
  linarith

theorem high_pointwise (y : ℝ) (hy : 3 ≤ y) : kernelReal 1 y ≤ 9*exp (-y-20) := by
  have hy0 : 0 ≤ y := by linarith
  have hey : 1 ≤ exp y := one_le_exp_iff.mpr hy0
  have hexpsq : exp (y/2)^2=exp y := by rw [pow_two,←exp_add]; congr 1; ring
  have hs : sqrt ((129/200:ℝ)*exp y+23/250) ≤ exp (y/2) := by
    apply (sqrt_le_left (exp_pos _).le).2
    rw [hexpsq]
    nlinarith
  have hlog : 1+y/28 ≤ exp (y/28) := by simpa [add_comm] using add_one_le_exp (y/28)
  have hp : exp (y/6)*(1+y/28) ≤ exp (y/4) := by
    calc
      _ ≤ exp (y/6)*exp (y/28) := by gcongr
      _ = exp (y/6+y/28) := (exp_add _ _).symm
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hequarter : 1 ≤ exp (y/4) := one_le_exp_iff.mpr (by linarith)
  have hehalf : exp (y/2) ≤ exp (3*y/4) := exp_le_exp.mpr (by linarith)
  let A := sqrt ((129/200:ℝ)*exp y+23/250)*
      (exp (y/6)*(1+(1:ℝ)*y/28)+137/100000)+(47/500000)*exp (y/2)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hfirst : sqrt ((129/200:ℝ)*exp y+23/250)*
      (exp (y/6)*(1+(1:ℝ)*y/28)+137/100000) ≤ 2*exp (3*y/4) := by
    calc
      _ ≤ exp (y/2)*(2*exp (y/4)) := by
        gcongr
        simp only [one_mul]
        linarith
      _ = _ := by rw [show exp (y/2)*(2*exp (y/4))=2*(exp (y/2)*exp (y/4)) by ring,←exp_add]; congr 2; ring
  have hA : A ≤ 3*exp (3*y/4) := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hehalf (by norm_num : (0:ℝ)≤47/500000),exp_pos (3*y/4)]
  have hsq : A^2 ≤ 9*exp (3*y/2) := by
    have hh : A^2 ≤ (3*exp (3*y/4))^2 := by gcongr
    have ee : exp (3*y/4)^2=exp (3*y/2) := by rw [pow_two,←exp_add]; congr 1; ring
    nlinarith
  have ht : 1+2*(y-3) ≤ exp (2*(y-3)) := by simpa [add_comm] using add_one_le_exp (2*(y-3))
  have hexp : exp (2*y) = exp 6*exp (2*(y-3)) := by rw [←exp_add]; congr 1; ring
  have hedom : (9/2:ℝ)*y+20 ≤ (601/2500)*exp (2*y) := by
    rw [hexp]
    have hpos : 0 ≤ 1+2*(y-3) := by linarith
    have he := mul_le_mul exp_six_lower ht hpos (exp_pos 6).le
    nlinarith
  calc
    kernelReal 1 y = exp (2*y-(601/2500)*exp (2*y))*A^2 := rfl
    _ ≤ exp (2*y-(601/2500)*exp (2*y))*(9*exp (3*y/2)) := by gcongr
    _ = 9*exp ((7/2)*y-(601/2500)*exp (2*y)) := by
      rw [show exp (2*y-(601/2500)*exp (2*y))*(9*exp (3*y/2))=
        9*(exp (2*y-(601/2500)*exp (2*y))*exp (3*y/2)) by ring,←exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by norm_num : (0:ℝ)≤9)

end WinnerReversDensity
