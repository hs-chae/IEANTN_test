/- Copyright (c)2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.HeightSemanticLink
import WinnerDensityA.Spectral
import DensityRay
namespace WinnerHeightSpectral
open Real Set MeasureTheory CH2QRH WinnerDensityA WinnerDensityA.Program
set_option maxHeartbeats 0

/-- The executed four-height row controls the actual common-height spectral
quantity on the entire logarithmic ray. There is no assumed spectral budget. -/
theorem height_spectral_ray
    (hrvm:ZeroCount.v1.rvm_error_bound) (hsmall:ZeroCount.v1.rvm_error_small)
    (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {n:ℕ} (hn:0<n) {L:ℝ} (hL:300≤L) :
    rawSpectral (exp (L/3)) (exp L)*exp (L/8)≤HeightProgram.rowCoefficient n 300 100 := by
  have h100: H≤exp (100:ℝ):=by
    have hh:=(CH2Section7A.exp_nat_bounds 44).1
    have he:exp (44:ℝ)≤exp 100:=exp_le_exp.mpr (by norm_num)
    norm_num [H] at hh ⊢
    linarith
  have ht:exp (100:ℝ)≤exp (L/3):=exp_le_exp.mpr (by linarith)
  have htH:=h100.trans ht
  have ht1:1≤exp (L/3):=by norm_num [H] at htH; linarith
  have h1000:1000≤exp (L/3):=by norm_num [H] at htH; linarith
  have ha:=grid_monotone hn
  have ha0:uniformGrid n 0=(3/4:ℝ):=by simp [uniformGrid]
  have han:uniformGrid n n=(7/8:ℝ):=by
    have hn0:(n:ℝ)≠0:=by exact_mod_cast hn.ne'
    unfold uniformGrid
    field_simp
    <;> ring
  have hQ:∀i≤n,(2*Real.pi/exp (L/3))*IEANTN.zetaZeroesSum
      (Ioo (uniformGrid n i) 1) (Ioc 0 (exp (L/3)))
      (fun rho↦exp (L/3)/Real.pi*(1/rho.im)+2)≤
        HeightProgram.mathEnvelope (uniformGrid n i) 100:=by
    intro i hi
    have hlo:(3/4:ℝ)≤uniformGrid n i:=by rw [←ha0];exact ha (Nat.zero_le i)
    have hhi:uniformGrid n i≤(7/8:ℝ):=by rw [←han];exact ha hi
    rw [height_envelope_link]
    exact WinnerHeightMoment.source_ordinate_envelope h hRH hlo hhi (by norm_num) h100 ht
  have hs:=spectral_grid_abstract hrvm hsmall hlow h1000 (exp_pos L)
    (by norm_num : (0:ℝ)≤300) (by simpa only [log_exp] using hL) hQRH
    (uniformGrid n) ha n ha0 han (fun s=>HeightProgram.mathEnvelope s 100) hQ
  have hb:=density_count_base_row (L₀:=300) (L:=L) (τ:=100) (t:=exp (L/3))
    (by norm_num) hL (by norm_num) ht1 (by rw [log_exp];norm_num;linarith)
  have hexp:(exp L)^((1:ℝ)/8)=exp (L/8):=by rw [rpow_def_of_pos (exp_pos L),log_exp];congr 1;ring
  rw [hexp,log_exp] at hs
  unfold HeightProgram.rowCoefficient
  linarith only [hs,hb]

/-- Concrete grid size used by the newly executed coefficient certificate. -/
theorem height_spectral_ray8192
    (hrvm:ZeroCount.v1.rvm_error_bound) (hsmall:ZeroCount.v1.rvm_error_small)
    (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L:ℝ} (hL:300≤L) :
    rawSpectral (exp (L/3)) (exp L)*exp (L/8)≤HeightProgram.rowCoefficient 8192 300 100 :=
  height_spectral_ray hrvm hsmall hlow h hRH hQRH (by norm_num) hL
#print axioms height_spectral_ray
end WinnerHeightSpectral
