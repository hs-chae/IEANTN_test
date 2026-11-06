/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.SignedHeight
import Mathlib.Tactic

namespace PVEvolutionA.Recovery.Gaussian
open Real
set_option maxHeartbeats 0

/-- The unchanged Gaussian weight in the signed source-moment adapter. -/
noncomputable def weight (y : ℝ) : ℝ := exp (2*y-(601/2500)*exp (2*y))

noncomputable def amplitude (m1 m2 h r0 sign y : ℝ) : ℝ :=
  sqrt (m1*exp y+m2)*(exp (y/6)*(1+sign*y/h)+r0)

/-- A finite algebraic majorant: its integration reduces to twelve universal
Gaussian moments, rather than a separate square-root quadrature per profile. -/
noncomputable def young (m1 m2 h r0 r1 ε sign y : ℝ) : ℝ :=
  weight y*((1+ε)*(m1*exp y+m2)*(exp (y/6)*(1+sign*y/h)+r0)^2+
    (1+1/ε)*r1^2*exp y)

theorem young_square (a b ε : ℝ) (hε : 0 < ε) :
    (a+b)^2 ≤ (1+ε)*a^2+(1+1/ε)*b^2 := by
  have hp : 0 ≤ (ε*a-b)^2/ε := div_nonneg (sq_nonneg _) hε.le
  have he : (a+b)^2+(ε*a-b)^2/ε = (1+ε)*a^2+(1+1/ε)*b^2 := by
    field_simp
    <;> ring
  linarith

theorem amplitude_sq (m1 m2 h r0 sign y : ℝ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) :
    amplitude m1 m2 h r0 sign y ^ 2 =
      (m1*exp y+m2)*(exp (y/6)*(1+sign*y/h)+r0)^2 := by
  unfold amplitude
  rw [mul_pow, sq_sqrt (by positivity : 0 ≤ m1*exp y+m2)]

theorem residual_sq (r1 y : ℝ) : (r1*exp (y/2))^2 = r1^2*exp y := by
  rw [mul_pow, ← exp_nat_mul]
  congr 1
  congr 1
  norm_num
  ring

theorem kernel_le_young (m1 m2 h r0 r1 ε y : ℝ)
    (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hε : 0 < ε) :
    WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1 y ≤
      young m1 m2 h r0 r1 ε (if y ≤ 0 then 0 else 1) y := by
  have hs : (if y ≤ 0 then (0:ℝ) else 1)*y = max y 0 := by
    split_ifs with hy
    · rw [max_eq_right hy]; ring
    · rw [max_eq_left (le_of_not_ge hy)]; ring
  have hp := young_square (amplitude m1 m2 h r0 (if y ≤ 0 then 0 else 1) y)
    (r1*exp (y/2)) ε hε
  rw [amplitude_sq _ _ _ _ _ _ hm1 hm2, residual_sq] at hp
  unfold WinnerBetaA.SignedHeight.kernel young weight amplitude at *
  rw [hs] at hp
  rw [hs]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (exp_pos _).le

/-- All numerical basis integrands use only exp and integer powers. -/
noncomputable def basis (n k : ℕ) (y : ℝ) : ℝ :=
  weight y*(exp (y/6))^n*y^k

noncomputable def reduced (m1 m2 h r0 r1 ε sign y : ℝ) : ℝ :=
  (1+ε)*(m1*basis 8 0 y+m2*basis 2 0 y+
    (2*sign/h)*(m1*basis 8 1 y+m2*basis 2 1 y)+
    (sign^2/h^2)*(m1*basis 8 2 y+m2*basis 2 2 y)+
    2*r0*(m1*basis 7 0 y+m2*basis 1 0 y)+
    (2*r0*sign/h)*(m1*basis 7 1 y+m2*basis 1 1 y)+
    r0^2*(m1*basis 6 0 y+m2*basis 0 0 y))+
  (1+1/ε)*r1^2*basis 6 0 y

theorem young_eq_reduced (m1 m2 h r0 r1 ε sign y : ℝ) :
    young m1 m2 h r0 r1 ε sign y = reduced m1 m2 h r0 r1 ε sign y := by
  have he : exp y = (exp (y/6))^6 := by
    rw [← exp_nat_mul]
    congr 1
    norm_num
    ring
  unfold young reduced basis
  rw [he]
  ring

#print axioms kernel_le_young
#print axioms young_eq_reduced
end PVEvolutionA.Recovery.Gaussian
