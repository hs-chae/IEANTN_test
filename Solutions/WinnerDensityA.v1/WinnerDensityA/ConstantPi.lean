/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.SharpPi
import WinnerBetaA.Theta
namespace WinnerDensityA
open Real IEANTN
open DudekPlattNumerics.v4.Numerics (poly_exp_decreasing exp_neg_nat_le)
/-- A constant-profile adapter retaining separate actual theta inputs at the anchor and target.
All continuation is proved; the only tail check is a closed scalar obligation. -/
theorem pi_constant_two_profiles {cA cB β a b δ cπ : ℝ}
    (hcA : 0≤cA) (hβ : 0<β) (ha : 1≤a) (hb : 0<b) (hab : a≤b)
    (hκ : 0<β-2/a) (hdec : 1≤β*b)
    (htail : b*exp (a-β*b)≤δ)
    (hcoef : cB+cA/(β-2/a)/b+7*δ≤cπ)
    (hθA : HasPowerLogBound Eθ cA 0 β (exp a))
    (hθB : HasPowerLogBound Eθ cB 0 β (exp b)) :
    HasPowerLogBound Eπ cπ 0 β (exp b) := by
  intro x hx
  have hx0 : 0<x := (exp_pos b).trans_le hx
  let L := log x
  have hL : b≤L := by
    have hh := log_le_log (exp_pos b) hx
    simpa [L] using hh
  have hLp : 0<L := hb.trans_le hL
  have heq : exp L=x := exp_log hx0
  have hA : 2≤exp a := by linarith [add_one_le_exp a]
  have hAx : exp a≤exp L := exp_le_exp.mpr (hab.trans hL)
  have hp := WinnerBetaA.sharp_pi_transfer hcA hA hAx
    (by simpa only [log_exp] using hκ) hθA
  have ht := hθB (exp L) (exp_le_exp.mpr hL)
  rw [log_exp,rpow_def_of_pos (exp_pos L),log_exp] at hp ht
  have hδ : 0≤δ := (by positivity : 0≤b*exp (a-β*b)).trans htail
  have hD := poly_exp_decreasing 1 (L0:=b) (c:=β) hb
    ((div_le_iff₀ hb).mpr (by simpa using hdec)) hL
  simp only [pow_one] at hD
  have htailL : L*exp (a-β*L)≤δ := by
    have hh := mul_le_mul_of_nonneg_left hD (exp_pos a).le
    have hi1 : L*exp (a-β*L)=exp a*(L*exp (-β*L)) := by
      rw [show a-β*L=a+(-β*L) by ring,exp_add]
      ring
    have hi2 : b*exp (a-β*b)=exp a*(b*exp (-β*b)) := by
      rw [show a-β*b=a+(-β*b) by ring,exp_add]
      ring
    rw [hi1]
    rw [hi2] at htail
    exact hh.trans htail
  have hea : 1≤exp a := by linarith [add_one_le_exp a]
  have hearly : (4*exp a+3)*L/exp L≤7*δ*exp (L*(β-1)) := by
    calc
      _ ≤ 7*exp a*L/exp L := by gcongr;linarith
      _ = 7*exp (L*(β-1))*(L*exp (a-β*L)) := by
        rw [show 7*exp (L*(β-1))*(L*exp (a-β*L))=
          7*L*(exp (L*(β-1))*exp (a-β*L)) by ring,←exp_add,
          show L*(β-1)+(a-β*L)=a-L by ring,exp_sub]
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left htailL (show 0≤7*exp (L*(β-1)) by positivity)]
  have hcoefL : cB+cA/(β-2/a)/L+7*δ≤cπ := by
    have hh : cA/(β-2/a)/L≤cA/(β-2/a)/b := by gcongr
    linarith
  have hfinal : Eπ (exp L)≤cπ*exp (L*(β-1)) := by
    have hh := mul_le_mul_of_nonneg_right hcoefL (exp_pos (L*(β-1))).le
    simp only [pow_zero,mul_one] at ht
    nlinarith
  rw [←heq,pow_zero,mul_one,rpow_def_of_pos (exp_pos L),log_exp]
  exact hfinal
end WinnerDensityA
#print axioms WinnerDensityA.pi_constant_two_profiles
