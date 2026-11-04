/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.GlobalCertificate
import WinnerDensityA.ConstantPi
import WinnerBetaA.SplitPi
namespace WinnerDensityA
open Real IEANTN
/-- Only the unchanged thirteen named CH2 source statements. -/
structure CH2Source : Prop where
  hfe : ZetaLogDeriv.v1.logDeriv_functional_equation
  hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip
  h24u : CH2.v2.proposition_2_4_upper
  h24l : CH2.v2.proposition_2_4_lower
  hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating
  hneg : ZetaLogDerivValues.v1.logDeriv_neg_one
  h2v : ZetaLogDerivValues.v1.logDeriv_two
  hv : ZetaLogDerivValues.v1.logDeriv_three_halves
  hcs : CotangentSeries.v1.cot_series_zeta_values
  hrvm : ZeroCount.v1.rvm_error_bound
  hsmall : ZeroCount.v1.rvm_error_small
  hlow : LowZeroes.v1.no_zeroes_below_first_ordinate
  hH : ZetaHadamard.v1.logDeriv_partial_fractions

theorem global_input (hFKS : FKS.v3.density_0618) :
    DensityInput (fun _ ↦ 9.795) (fun _ ↦ 4.465) := by
  intro σ t hσ hσ' ht
  have ht' : 3*(10:ℝ)^(12:ℕ)≤t := by norm_num at *;exact ht
  exact hFKS σ t hσ hσ' ht'

/-- Any executed coefficient provider for the new grid can feed the actual psi ray. -/
theorem psi_profile (hs : CH2Source) (c d : ℝ → ℝ) (hD : DensityInput c d)
    (hc : ∀ σ ∈ Set.Icc (3/4:ℝ) (7/8),0≤c σ ∧ 0≤d σ)
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8))
    {L C : ℝ} (hL : 64≤L) (hk : (100:ℝ)≤(7/10)*L) (hsep : 34≤100-L/8)
    {n : ℕ} (hn : 0<n)
    (hNumerical : rowCoefficient c d (Program.uniformGrid n) n L 100≤C) :
    HasPowerLogBound Eψ C 0 (7/8) (exp L) := by
  intro x hx
  have hx0 : 0<x := (exp_pos L).trans_le hx
  have h := psi_row_normalized hs.hfe hs.hdig hs.h24u hs.h24l hs.hk hs.hneg hs.h2v hs.hv hs.hcs hs.hrvm hs.hsmall hs.hlow hs.hH c d hD hc hRH
    (Program.uniformGrid n) (Program.grid_monotone hn) n (by norm_num [Program.uniformGrid])
    (by norm_num [Program.uniformGrid];field_simp;ring) hL (by norm_num) hk hsep hx hqrh
  have hp := psi_of_normalized hx0 (h.trans hNumerical)
  simpa only [pow_zero,mul_one,show (7/8:ℝ)-1=-1/8 by norm_num] using hp

theorem psi200 (hs : CH2Source) (hFKS : FKS.v3.density_0618)
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eψ 0.016574 0 (7/8) (exp 200) := by
  exact psi_profile hs _ _ (global_input hFKS) (by intro σ hσ;norm_num) hRH hqrh
    (by norm_num) (by norm_num) (by norm_num) (by decide : 0<(4096:ℕ)) (by convert GlobalCertificate.coefficient200 using 1 <;> norm_num)

theorem psi300 (hs : CH2Source) (hFKS : FKS.v3.density_0618)
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eψ 0.013106 0 (7/8) (exp 300) := by
  exact psi_profile hs _ _ (global_input hFKS) (by intro σ hσ;norm_num) hRH hqrh
    (by norm_num) (by norm_num) (by norm_num) (by decide : 0<(4096:ℕ)) (by convert GlobalCertificate.coefficient300 using 1 <;> norm_num)

theorem theta200 (hs : CH2Source) (hFKS : FKS.v3.density_0618)
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eθ (0.016574+1/10^12) 0 (7/8) (exp 200) := by
  apply WinnerBetaA.theta_from_psi (by norm_num : 0<(200:ℝ)) (by norm_num)
  · have h := WinnerBetaA.tiny_theta_slack (β:=(7/8:ℝ)) (L₀:=(200:ℝ)) le_rfl le_rfl
    convert h using 1 <;> norm_num
  · exact psi200 hs hFKS hRH hqrh

theorem theta300 (hs : CH2Source) (hFKS : FKS.v3.density_0618)
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eθ (0.013106+1/10^12) 0 (7/8) (exp 300) := by
  apply WinnerBetaA.theta_from_psi (by norm_num : 0<(300:ℝ)) (by norm_num)
  · convert WinnerBetaA.tiny_theta_slack (β:=(7/8:ℝ)) (L₀:=(300:ℝ)) le_rfl (by norm_num) using 1 <;> norm_num
  · exact psi300 hs hFKS hRH hqrh

/-- A new complete source-linked prime-error route; strongest comparison is separate. -/
theorem pi300 (hs : CH2Source) (hFKS : FKS.v3.density_0618)
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ 0.013170 0 (7/8) (exp 300) := by
  apply pi_constant_two_profiles (a:=(200:ℝ)) (b:=(300:ℝ)) (δ:=(1/10^14:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_ (by norm_num) (theta200 hs hFKS hRH hqrh) (theta300 hs hFKS hRH hqrh)
  have h1 : exp ((200:ℝ)-(7/8)*300)≤exp (-(60:ℝ)) := exp_le_exp.mpr (by norm_num)
  have h2 := DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 60
  norm_num at h2 ⊢
  nlinarith
#print axioms pi300
end WinnerDensityA
