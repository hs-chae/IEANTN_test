/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.Numerical
import PVEvolutionA.Recovery.ManyMoment
import WinnerDensityA.HeightSpectral
namespace PVEvolutionA.Recovery.Spectral
open Real Set MeasureTheory CH2QRH WinnerDensityA WinnerDensityA.Program
set_option maxHeartbeats 0
/-- Variable ray onset and a nonuniform partition, under the original fixed
source package. The truncation height stays exp(L/3); it is never finite RH. -/
theorem graded_spectral_ray
    (accepted : ∀j:Fin 18,WinnerProgramA.acceptUpper (GaussianBasis.output j) [(GaussianBasis.spec j).cap]=true)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hsmall:ZeroCount.v1.rvm_error_small)
    (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {n:ℕ} (hn:0<n) {L0 L:ℝ} (h0:300≤L0) (hL:L0≤L) :
    rawSpectral (exp (L/3)) (exp L)*exp (L/8)≤Numerical.coefficient n L0 100 := by
  have hL300 : 300≤L := h0.trans hL
  have h100: H≤exp (100:ℝ):=by
    have hh:=(CH2Section7A.exp_nat_bounds 44).1
    have he:exp (44:ℝ)≤exp 100:=exp_le_exp.mpr (by norm_num)
    norm_num [H] at hh ⊢
    linarith
  have ht:exp (100:ℝ)≤exp (L/3):=exp_le_exp.mpr (by linarith)
  have htH:=h100.trans ht
  have ht1:1≤exp (L/3):=by norm_num [H] at htH; linarith
  have h1000:1000≤exp (L/3):=by norm_num [H] at htH; linarith
  have ha:=graded_monotone n
  have ha0:=graded_zero hn
  have han:=graded_last n
  have hQ:∀i≤n,(2*Real.pi/exp (L/3))*IEANTN.zetaZeroesSum
      (Ioo (gradedGrid n i) 1) (Ioc 0 (exp (L/3)))
      (fun rho↦exp (L/3)/Real.pi*(1/rho.im)+2)≤
        Model.envelope (gradedGrid n i) 100:=by
    intro i hi
    have hlo:(3/4:ℝ)≤gradedGrid n i:=by rw [←ha0];exact ha (Nat.zero_le i)
    have hhi:gradedGrid n i≤(7/8:ℝ):=by rw [←han];exact ha hi
    exact Model.source_ordinate_envelope accepted h hRH hlo hhi (by norm_num) h100 ht
  have hs:=spectral_grid_abstract hrvm hsmall hlow h1000 (exp_pos L)
    (by linarith : (0:ℝ)≤L0) (by simpa only [log_exp] using hL) hQRH
    (gradedGrid n) ha n ha0 han (fun s=>Model.envelope s 100) hQ
  have hdiv : (L0/3)/L0=(1/3:ℝ) := by field_simp
  have hb:=density_count_base_row (L₀:=L0) (L:=L) (τ:=L0/3) (t:=exp (L/3))
    (by linarith) hL (by linarith) ht1 (by rw [log_exp,hdiv];linarith)
  have hexp:(exp L)^((1:ℝ)/8)=exp (L/8):=by rw [rpow_def_of_pos (exp_pos L),log_exp];congr 1;ring
  rw [hexp,log_exp] at hs
  unfold Numerical.coefficient
  linarith only [hs,hb]
#print axioms graded_spectral_ray
end PVEvolutionA.Recovery.Spectral
