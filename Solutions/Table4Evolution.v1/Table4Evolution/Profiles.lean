/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.Instance
import FKS2Table4.Math
import IEANTN.Nodes.FKS2.v8.Conclusions

/-!
# The three input profiles

| profile | `s` | `mOf lo` | from |
|---|---|---|---|
| QRH, `Q(L) = L²/283·e^{-L/8}` | `1/8` | `lo²/283` | `QRHCH2.v5.psi_refined_bound` (via `FKS2Table4.theta_input`) |
| QRH-free step (FKS2 Table 3) | `0` | `1.6930, 1.6882, 1.6837, 1.6795 ·10⁻¹²` | the four `FKS2.v8.table3_theta_*` rows |
| a power bound `K·x^{-1/8}` | `1/8` | `K` | `HasPowerLogBound Eθ K 0 (7/8) (exp 300)` |
-/

namespace Table4Evolution

open Real IEANTN FKS2Table4

def qrhM (lo : ℚ) : ℚ := lo ^ 2 / 283

theorem profile_qrh (hpsi : QRHCH2.v5.psi_refined_bound) : ProfileOK (1 / 8) qrhM := by
  intro lo hlo
  refine ⟨by unfold qrhM; positivity, fun t ht => ?_⟩
  have h := theta_on_ray (theta_input hpsi) (by exact_mod_cast hlo : (300 : ℝ) ≤ lo) ht
  have hq : Q (lo : ℝ) = (qrhM lo : ℝ) * exp (-(((1 / 8 : ℚ) : ℝ) * lo)) := by
    unfold Q qrhM; push_cast; ring_nf
  rwa [hq] at h

/-- The QRH-free step profile, by left endpoint. -/
def stepM (lo : ℚ) : ℚ :=
  if lo < 310 then 1.6930e-12 else if lo < 320 then 1.6882e-12 else if lo < 330 then 1.6837e-12
  else 1.6795e-12

theorem profile_step (h300 : FKS2.v8.table3_theta_300) (h310 : FKS2.v8.table3_theta_310)
    (h320 : FKS2.v8.table3_theta_320) (h330 : FKS2.v8.table3_theta_330) : ProfileOK 0 stepM := by
  intro lo hlo
  refine ⟨by unfold stepM; split_ifs <;> norm_num, fun t ht => ?_⟩
  simp only [Rat.cast_zero, zero_mul, neg_zero, exp_zero, mul_one]
  have hge : ∀ b : ℚ, b ≤ lo → exp (b : ℝ) ≤ t := fun b hb =>
    (exp_le_exp.mpr (by exact_mod_cast hb)).trans ht
  unfold stepM
  split_ifs with h1 h2 h3
  · have := h300 t (by simpa using hge 300 hlo); norm_num at this ⊢; exact this
  · have := h310 t (by simpa using hge 310 (not_lt.mp h1)); norm_num at this ⊢; exact this
  · have := h320 t (by simpa using hge 320 (not_lt.mp h2)); norm_num at this ⊢; exact this
  · have := h330 t (by simpa using hge 330 (not_lt.mp h3)); norm_num at this ⊢; exact this

theorem profile_power {K : ℚ} (hK : 0 ≤ K) (hθ : HasPowerLogBound Eθ (K : ℝ) 0 (7 / 8) (exp 300)) :
    ProfileOK (1 / 8) (fun _ => K) := by
  intro lo hlo
  refine ⟨hK, fun t ht => ?_⟩
  have hlo' : (300 : ℝ) ≤ lo := by exact_mod_cast hlo
  have ht300 : exp 300 ≤ t := (exp_le_exp.mpr hlo').trans ht
  have ht0 : 0 < t := (exp_pos _).trans_le ht
  have hb := hθ t ht300
  simp only [pow_zero, mul_one] at hb
  have hlog : (lo : ℝ) ≤ log t := by simpa using log_le_log (exp_pos _) ht
  have hpow : t ^ ((7 : ℝ) / 8 - 1) ≤ exp (-(((1 / 8 : ℚ) : ℝ) * lo)) := by
    rw [rpow_def_of_pos ht0]
    apply exp_le_exp.mpr
    push_cast
    nlinarith
  have hK' : (0 : ℝ) ≤ K := by exact_mod_cast hK
  calc Eθ t ≤ (K : ℝ) * t ^ ((7 : ℝ) / 8 - 1) := hb
    _ ≤ (K : ℝ) * exp (-(((1 / 8 : ℚ) : ℝ) * lo)) := by gcongr

end Table4Evolution
