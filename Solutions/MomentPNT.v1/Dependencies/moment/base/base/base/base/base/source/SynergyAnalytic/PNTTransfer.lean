import SynergyAnalytic.ActualSpectral
import DensityRay
import WinnerDensityA.DirectRHSplitNormalized
import WinnerDensityA.LowRHKernel
namespace SynergyAnalytic
open Real Set MeasureTheory IEANTN WinnerDensityA WinnerDirectKernel CH2QRH
set_option maxHeartbeats 0

noncomputable def spectralBase (L0 tau : ℝ) : ℝ :=
  Real.exp (-L0/8)*((tau+(1:ℝ)/10^9)^2/(2*Real.pi)+
    (2+1/Real.pi)*(tau+(1:ℝ)/10^9))

/-- The full prime-number theorem transfer for a continuous ordinate envelope.
All numerical work remains explicit: the envelope provider and one scalar
budget must be discharged by the application. This theorem adds no new
analytic assumption, and preserves CHJ/finite-RH/QRH inputs exactly. -/
theorem pi_from_continuous_ordinate_envelope
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small) (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
    {L0 C : ℝ} (h0 : 300≤L0) (Q : ℝ→ℝ) (hQc : Continuous Q)
    (hEnv : ∀{s t:ℝ},s∈Icc (3/4:ℝ) (7/8) → Real.exp (L0/3)≤t →
      (2*Real.pi/t)*IEANTN.zetaZeroesSum (Ioo s 1) (Ioc 0 t)
        (fun rho=>t/Real.pi*(1/rho.im)+2)≤Q s)
    (hc : spectralBase L0 (L0/3)+pairedFunctional (7/8) (1/8) L0 Q≤C) :
    HasPowerLogBound Eπ ((1+1/1000000000)*C+1/1000000000000+1/100000000)
      0 (7/8) (Real.exp L0) := by
  apply rh_pi_ray_of_budgets hCHJ hQRH hlow h0
  · intro L hL
    have hL300 : 300≤L := h0.trans hL
    have h1000 : (1000:ℝ)≤Real.exp (L/3) := by
      calc
        (1000:ℝ) ≤ 2^100 := by norm_num
        _ ≤ (Real.exp 1)^100 := pow_le_pow_left₀ (by norm_num)
          (by linarith [Real.add_one_le_exp (1:ℝ)]) 100
        _ = Real.exp 100 := by rw [←Real.exp_nat_mul];norm_num
        _ ≤ Real.exp (L/3) := Real.exp_le_exp.mpr (by linarith)
    have ht : Real.exp (L0/3)≤Real.exp (L/3) := Real.exp_le_exp.mpr (by linarith)
    have hs := actual_spectral_from_continuous_envelope hrvm hsmall hlow h1000
      (Real.exp_pos L) (by linarith : 0≤L0) (by simpa only [Real.log_exp] using hL)
      hQRH Q hQc (fun s hs=>hEnv hs ht)
    have hbase := density_count_base_row (L₀:=L0) (L:=L) (τ:=L0/3) (t:=Real.exp (L/3))
      (by linarith) hL (by linarith) (by linarith) (by
        rw [Real.log_exp]
        have hdiv : (L0/3)/L0=(1/3:ℝ) := by field_simp
        rw [hdiv]
        linarith)
    have hexp : (Real.exp L)^((1:ℝ)/8)=Real.exp (L/8) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp]
      congr 1
      ring
    rw [hexp,Real.log_exp] at hs
    exact (hs.trans (add_le_add hbase le_rfl)).trans hc
  · intro L hL
    exact low_paired_kernel_tiny hQRH hRH hrvm hsmall hlow (h0.trans hL)

#print axioms pi_from_continuous_ordinate_envelope
end SynergyAnalytic
