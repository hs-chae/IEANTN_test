/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.Interval.MomentRay
import E1NPlus.Scalars

namespace E1NPlus
open Real Set MeasureTheory

noncomputable abbrev c : ℝ := 43 / 50
noncomputable abbrev alpha : ℝ := 79 / 100
noncomputable abbrev eta : ℝ := 21 / 100
noncomputable abbrev K : ℝ := 72091 / 10000
noncomputable abbrev B : ℝ := 5458 / 1000
noncomputable abbrev p (s : ℝ) : ℝ := 8 * (1-s) / 3
noncomputable abbrev q (s : ℝ) : ℝ := 5 - 2*s
noncomputable abbrev b (s : ℝ) : ℝ := 1-p s

noncomputable def gap (L : ℝ) : ℝ := c * exp (alpha*L)
noncomputable def delta (L : ℝ) : ℝ := c * exp (-eta*L)
noncomputable def U (L : ℝ) : ℝ := k * exp (eta*L)
noncomputable def truncHeight (L : ℝ) : ℝ := (600000/43 : ℝ)*L*exp (eta*L)
noncomputable def V (L : ℝ) : ℝ := 2*truncHeight L
noncomputable def profileHeight : ℝ := 3*(10:ℝ)^12*exp 4
noncomputable def ulog (L : ℝ) : ℝ := eta*L+log k
noncomputable def coeff (s : ℝ) : ℝ := K*exp (B*(s-7/8))
noncomputable def densityMajorant (s t : ℝ) : ℝ :=
  coeff s*t^(p s)*log t^(q s)+6*log t^2
noncomputable def poly4 (s u : ℝ) : ℝ :=
  u^(q s)/b s*E1FrozenN.Interval.factor4 s u
noncomputable def moment (s H : ℝ) : ℝ :=
  coeff s*CH2QRH.densityMomentMain s H+6*((log H^2+2*log H+2)/H)
noncomputable def high (L : ℝ) : ℝ :=
  2*U L*L*∫s in (3/4:ℝ)..(7/8:ℝ),exp (-(1-s)*L)*moment s (U L)
noncomputable def low (L : ℝ) : ℝ :=
  (k/Real.pi)*exp (-L/25)*(log (V L)+(log (V L)^2-(ulog L)^2)/2)

theorem coeff_nonneg (s : ℝ) : 0 ≤ coeff s := by unfold coeff K; positivity

theorem moment_bound {s H T : ℝ} (hH : 1 < H) (hHT : H ≤ T)
    (hs : (3/4:ℝ) ≤ s) (hs' : s ≤ 7/8) :
    densityMajorant s T/T+(∫t in H..T,densityMajorant s t/t^2) ≤ moment s H := by
  have h1 := CH2QRH.power_log_tail_four (p:=p s) (q:=q s) hH hHT
    (by dsimp [p];linarith) (by dsimp [p];linarith)
    (by dsimp [q];linarith) (by dsimp [q];linarith)
  change _ ≤ CH2QRH.densityMomentMain s H at h1
  have h2 := CH2QRH.log_square_reciprocal_tail hH hHT
  have hi1 := CH2QRH.power_log_intervalIntegrable (p:=p s) (q:=q s) hH hHT
  have hi2 := CH2QRH.power_log_intervalIntegrable (p:=0) (q:=2) hH hHT
  have he : (fun t:ℝ=>densityMajorant s t/t^2)=
      (fun t:ℝ=>coeff s*(t^(p s)*log t^(q s)/t^2)+6*(t^(0:ℝ)*log t^(2:ℝ)/t^2)) := by
    funext t
    simp only [densityMajorant,Real.rpow_zero,Real.rpow_two]
    ring
  rw [he,intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  simp only [Real.rpow_zero,Real.rpow_two,one_mul]
  calc
    _ = coeff s*(T^(p s)*log T^(q s)/T+∫t in H..T,t^(p s)*log t^(q s)/t^2)+
        6*(log T^2/T+∫t in H..T,log t^2/t^2) := by unfold densityMajorant;ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 (coeff_nonneg s))
      (mul_le_mul_of_nonneg_left h2 (by norm_num))

theorem moment_continuousOn {H : ℝ} (hH : 1 < H) :
    ContinuousOn (fun s:ℝ=>moment s H) (Icc (3/4:ℝ) (7/8:ℝ)) := by
  intro s hs
  have hH0 : 0 < H := by linarith
  have hl : 0 < log H := log_pos hH
  have hb : 0 < 1-8*(1-s)/3 := by linarith [hs.1]
  have hb0 := hb.ne'
  have hbu := mul_ne_zero hb0 hl.ne'
  unfold moment coeff CH2QRH.densityMomentMain
  dsimp only
  fun_prop (disch := first | assumption | positivity)

end E1NPlus
#print axioms E1NPlus.moment_bound
