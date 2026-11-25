/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace RH080.SineBridge
open Real

def foldAngle (m : ℕ) : ℕ × Bool :=
  let r := m % 512
  let flipped := 256 < r
  let r := if flipped then 512-r else r
  (if 128 < r then 256-r else r, flipped)

theorem foldAngle_mem (m : ℕ) : (foldAngle m).1 ≤ 128 := by
  have hm := Nat.mod_lt m (by decide : 0 < 512)
  simp only [foldAngle]
  split <;> split <;> simp_all <;> omega

theorem sin_mod512 (m : ℕ) :
    sin (π*(m : ℝ)/256) = sin (π*(m%512 : ℕ)/256) := by
  have heq : (m : ℝ) = (m%512 : ℕ) + 512*(m/512 : ℕ) := by
    exact_mod_cast (Nat.mod_add_div m 512).symm
  have hangle : π*(m : ℝ)/256 = π*(m%512 : ℕ)/256 + (m/512 : ℕ)*(2*π) := by
    rw [heq]
    ring
  rw [hangle]
  exact sin_add_nat_mul_two_pi _ _

theorem sin_foldAngle (m : ℕ) :
    sin (π*(m : ℝ)/256) =
      if (foldAngle m).2 then -sin (π*((foldAngle m).1 : ℝ)/256)
      else sin (π*((foldAngle m).1 : ℝ)/256) := by
  rw [sin_mod512]
  have hm : m%512 < 512 := Nat.mod_lt _ (by decide)
  by_cases hf : 256 < m%512
  · have hc : ((512-m%512 : ℕ) : ℝ) = 512-(m%512 : ℕ) := by
      rw [Nat.cast_sub (by omega)]; norm_num
    by_cases hr : 128 < 512-m%512
    · have hd : ((256-(512-m%512) : ℕ) : ℝ) = 256-((512-m%512 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]; norm_num
      have h1 := sin_two_pi_sub (π*(m%512 : ℕ)/256)
      have h2 := sin_pi_sub (π*(512-(m%512 : ℕ))/256)
      have e1 : 2*π-π*(m%512 : ℕ)/256 = π*(512-(m%512 : ℕ))/256 := by ring
      have e2 : π-π*(512-(m%512 : ℕ))/256 = π*(256-(512-(m%512 : ℕ)))/256 := by ring
      rw [e1] at h1
      rw [e2] at h2
      have hcalc : sin (π*(m%512 : ℕ)/256) = -sin (π*((256-(512-m%512) : ℕ) : ℝ)/256) := by
        rw [hd,hc]; linarith
      simpa [foldAngle,hf,hr] using hcalc
    · have h := sin_two_pi_sub (π*(m%512 : ℕ)/256)
      have e : 2*π-π*(m%512 : ℕ)/256 = π*(512-(m%512 : ℕ))/256 := by ring
      rw [e] at h
      have hcalc : sin (π*(m%512 : ℕ)/256) = -sin (π*((512-m%512 : ℕ) : ℝ)/256) := by
        rw [hc]; linarith
      simpa [foldAngle,hf,hr] using hcalc
  · by_cases hr : 128 < m%512
    · have hc : ((256-m%512 : ℕ) : ℝ) = 256-(m%512 : ℕ) := by
        rw [Nat.cast_sub (by omega)]; norm_num
      have h := sin_pi_sub (π*(m%512 : ℕ)/256)
      have e : π-π*(m%512 : ℕ)/256 = π*(256-(m%512 : ℕ))/256 := by ring
      rw [e] at h
      have hcalc : sin (π*(m%512 : ℕ)/256) = sin (π*((256-m%512 : ℕ) : ℝ)/256) := by
        rw [hc]; exact h.symm
      simpa [foldAngle,hf,hr] using hcalc
    · simp [foldAngle,hf,hr]

end RH080.SineBridge
#print axioms RH080.SineBridge.sin_foldAngle
