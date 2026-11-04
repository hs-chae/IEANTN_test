/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.GlobalAssembly
import WinnerDensityA.ReversCertificate
namespace WinnerDensityA.Revers
open Real IEANTN
/-- Internal consumer only. SourceResult supplies this density premise from
original source relations and the newly checked Gaussian calculation. -/
theorem psi200 (hs : CH2Source) (hD : DensityInput (ModelProgram.modelC (15/2) (547/100)) (fun _ ↦ 6))
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eψ 0.012097 0 (7/8) (exp 200) := by
  exact psi_profile hs _ _ hD (by intro σ hσ;constructor;exact le_of_lt (by unfold ModelProgram.modelC;positivity);norm_num) hRH hqrh
    (by norm_num) (by norm_num) (by norm_num) (by decide : 0<(4096:ℕ)) (by convert ReversCertificate.coefficient200 using 1 <;> norm_num)

theorem psi300 (hs : CH2Source) (hD : DensityInput (ModelProgram.modelC (15/2) (547/100)) (fun _ ↦ 6))
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eψ 0.009782 0 (7/8) (exp 300) := by
  exact psi_profile hs _ _ hD (by intro σ hσ;constructor;exact le_of_lt (by unfold ModelProgram.modelC;positivity);norm_num) hRH hqrh
    (by norm_num) (by norm_num) (by norm_num) (by decide : 0<(4096:ℕ)) (by convert ReversCertificate.coefficient300 using 1 <;> norm_num)

theorem theta200 (hs : CH2Source) (hD : DensityInput (ModelProgram.modelC (15/2) (547/100)) (fun _ ↦ 6))
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eθ (0.012097+1/10^12) 0 (7/8) (exp 200) := by
  apply WinnerBetaA.theta_from_psi (by norm_num : 0<(200:ℝ)) (by norm_num)
  · have h := WinnerBetaA.tiny_theta_slack (β:=(7/8:ℝ)) (L₀:=(200:ℝ)) le_rfl le_rfl
    convert h using 1 <;> norm_num
  · exact psi200 hs hD hRH hqrh

theorem theta300 (hs : CH2Source) (hD : DensityInput (ModelProgram.modelC (15/2) (547/100)) (fun _ ↦ 6))
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eθ (0.009782+1/10^12) 0 (7/8) (exp 300) := by
  apply WinnerBetaA.theta_from_psi (by norm_num : 0<(300:ℝ)) (by norm_num)
  · convert WinnerBetaA.tiny_theta_slack (β:=(7/8:ℝ)) (L₀:=(300:ℝ)) le_rfl (by norm_num) using 1 <;> norm_num
  · exact psi300 hs hD hRH hqrh

/-- A new complete source-linked prime-error route; strongest comparison is separate. -/
theorem pi300 (hs : CH2Source) (hD : DensityInput (ModelProgram.modelC (15/2) (547/100)) (fun _ ↦ 6))
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ 0.009830 0 (7/8) (exp 300) := by
  apply pi_constant_two_profiles (a:=(200:ℝ)) (b:=(300:ℝ)) (δ:=(1/10^14:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_ (by norm_num) (theta200 hs hD hRH hqrh) (theta300 hs hD hRH hqrh)
  have h1 : exp ((200:ℝ)-(7/8)*300)≤exp (-(60:ℝ)) := exp_le_exp.mpr (by norm_num)
  have h2 := DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 60
  norm_num at h2 ⊢
  nlinarith
#print axioms pi300
end WinnerDensityA.Revers
