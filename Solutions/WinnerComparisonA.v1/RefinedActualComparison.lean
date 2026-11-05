/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongFullComparison
import WinnerDensityA.DirectRHResult
namespace WinnerStrongEnvelope
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0
/-- Give the old witness the same refined direct-prime transport and low-RH
kernel treatment. Its original density family remains the source layer. -/
noncomputable def oldSharedRHAllowance (L : ℝ) : ℝ :=
  (1+1/1000000000)*(oldDensityComponent L+oldEndpointAllowance L+oldLowAllowance L)+
    1/1000000000000+1/100000000
 theorem density_le_shared_RH {L : ℝ} (hL : 300≤L) :
    oldDensityComponent L≤oldSharedRHAllowance L := by
  have hd:=density_component_nonnegative hL
  have he:=endpoint_nonnegative hL
  have hl:=low_nonnegative hL
  unfold oldSharedRHAllowance
  nlinarith
 theorem shared_RH_lower {L : ℝ} (hL : 300≤L) (hL' : L≤30001/100) :
    (18973/2000000:ℝ)≤oldSharedRHAllowance L :=
  benchmark_rounded_lower.trans ((benchmark_le_full_density hL hL').trans (density_le_shared_RH hL))
 theorem shared_RH_margin {L : ℝ} (hL : 300≤L) (hL' : L≤30001/100) :
    (3/250000:ℝ)≤oldSharedRHAllowance L-(473723/50000000) := by
  have hh:=shared_RH_lower hL hL'
  linarith
/-- Actual normalized prime error with strict comparison under the same refined
kernel treatment on both sides. No new computation or analytic oracle. -/
 theorem refined_actual_prime_comparison
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    ∀x∈Set.Icc (exp 300) (exp (30001/100)),
      Eπ x≤(473723/50000000:ℝ)*x^(-(1:ℝ)/8) ∧
      (473723/50000000:ℝ)*x^(-(1:ℝ)/8)<oldSharedRHAllowance (log x)*x^(-(1:ℝ)/8) := by
  intro x hx
  have hx0 : 0<x := (exp_pos _).trans_le hx.1
  have hL : 300≤log x := by simpa only [log_exp] using log_le_log (exp_pos 300) hx.1
  have hL' : log x≤30001/100 := by simpa only [log_exp] using log_le_log hx0 hx.2
  constructor
  · have hp:=WinnerDensityA.HeightRHFinal.source_pi_00947446 hCHJ hrvm hsmall hlow h hRH hQRH x hx.1
    norm_num at hp ⊢
    exact hp
  · apply mul_lt_mul_of_pos_right _ (rpow_pos_of_pos hx0 _)
    have ho:=shared_RH_lower hL hL'
    linarith
#print axioms shared_RH_margin
#print axioms refined_actual_prime_comparison
end WinnerStrongEnvelope
