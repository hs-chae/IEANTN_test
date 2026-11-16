/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.MomentSourceInputs.v1.Conclusions
import IEANTN.Nodes.MomentPNT.v1.Conclusions
import IEANTN.Nodes.PlattTrudgian.v1.Conclusions
import IEANTN.Nodes.OpenAIQRH.v1.Conclusions
import SynergyMomentCHi.FinalProgram
import SynergyVector300.Real
import MomentPNTDerived

/-! Exact graph adapters. The moment conclusions consume the reads of the two
complete source programs through FinalProgram, not an unrelated numerical
certificate accompanied by an unused source-call proposition. The stronger
direct-vector control keeps its separate ordinary-kernel classification. -/

open MomentSourceInputs.v1
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
noncomputable section

private theorem primary
    (low : low_zeta) (revers : revers_zeta) (mean : mollifier_mean_square)
    (smooth : source_smoothing) (right : source_right_moment)
    (rectangle : source_rectangle) (unsmooth : source_unsmoothing)
    (interpolation : source_interpolation) :
    WinnerNewHeightSource.PrimaryInputs (3681 / 10000) (3599 / 10000) :=
  ⟨low, revers, mean, smooth, right, rectangle, unsmooth, interpolation⟩

private theorem finite_rh (h : PlattTrudgian.v1.rh_up_to) :
    IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height := by
  convert h using 1 <;> norm_num [PlattTrudgian.v1.rh_up_to, WinnerOriginalScalars.height]

section Inputs
variable
    (low : low_zeta) (revers : revers_zeta) (mean : mollifier_mean_square)
    (smooth : source_smoothing) (right : source_right_moment)
    (rectangle : source_rectangle) (unsmooth : source_unsmoothing)
    (interpolation : source_interpolation) (chj : original_chj)
    (rvm : ZeroCount.v1.rvm_error_bound) (small : ZeroCount.v1.rvm_error_small)
    (first : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (rh : PlattTrudgian.v1.rh_up_to) (qrh : OpenAIQRH.v1.zeta_seven_eighths)

include low revers mean smooth right rectangle unsmooth interpolation chj rvm small first rh qrh

private theorem source_results :
    MomentPNT.v1.moment_pi ∧ MomentPNT.v1.moment_psi ∧ MomentPNT.v1.moment_future_pi := by
  let platform : ScopedIO.WorldIO.Platform := ⟨⟨0, 0, []⟩⟩
  let stream : ScopedIO.Stream := ⟨[], 0, false⟩
  obtain ⟨massTrace, massFinal, momentTrace, momentFinal, massExecution, momentExecution,
      ant, future⟩ := SynergyMomentCHi.FinalProgram.source_pi_psi_and_future platform stream
    (primary low revers mean smooth right rectangle unsmooth interpolation)
    chj rvm small first (finite_rh rh) qrh
  exact ⟨ant.1, ant.2, future⟩

private theorem kernel_results :
    MomentPNT.v1.kernel_control_pi ∧ MomentPNT.v1.kernel_control_psi :=
  SynergyVector300.kernel_pi_psi_300
    (primary low revers mean smooth right rectangle unsmooth interpolation)
    chj rvm small first (finite_rh rh) qrh

theorem MomentPNT.v1.challenge_moment_pi : MomentPNT.v1.moment_pi :=
  (source_results low revers mean smooth right rectangle unsmooth interpolation chj
    rvm small first rh qrh).1

theorem MomentPNT.v1.challenge_moment_psi : MomentPNT.v1.moment_psi :=
  (source_results low revers mean smooth right rectangle unsmooth interpolation chj
    rvm small first rh qrh).2.1

theorem MomentPNT.v1.challenge_kernel_control_pi : MomentPNT.v1.kernel_control_pi :=
  (kernel_results low revers mean smooth right rectangle unsmooth interpolation chj
    rvm small first rh qrh).1

theorem MomentPNT.v1.challenge_kernel_control_psi : MomentPNT.v1.kernel_control_psi :=
  (kernel_results low revers mean smooth right rectangle unsmooth interpolation chj
    rvm small first rh qrh).2

theorem MomentPNT.v1.challenge_moment_future_pi : MomentPNT.v1.moment_future_pi :=
  (source_results low revers mean smooth right rectangle unsmooth interpolation chj
    rvm small first rh qrh).2.2

end Inputs
end

#print axioms MomentPNT.v1.challenge_moment_pi
#print axioms MomentPNT.v1.challenge_moment_psi
#print axioms MomentPNT.v1.challenge_kernel_control_pi
#print axioms MomentPNT.v1.challenge_kernel_control_psi
#print axioms MomentPNT.v1.challenge_moment_future_pi

/-- Derived transport uses only the already stated moment future profile. -/
theorem MomentPNT.v1.challenge_moment_prime_rich
    (h : MomentPNT.v1.moment_future_pi) : MomentPNT.v1.moment_prime_rich := by
  intro x hx
  exact MomentPNTDerived.moment_prime_rich h hx
#print axioms MomentPNT.v1.challenge_moment_prime_rich
