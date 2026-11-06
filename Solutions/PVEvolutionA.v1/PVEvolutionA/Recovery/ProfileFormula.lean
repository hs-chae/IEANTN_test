/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.ProfileScalars
import PVEvolutionA.Recovery.GaussianBudget
import PVEvolutionA.Recovery.GaussianBasisCaps
import WinnerDensityA.HeightContext

namespace PVEvolutionA.Recovery.Profile
open Real Set MeasureTheory LeanCert.Core LeanCert.Engine WinnerOriginalScalars
set_option maxHeartbeats 0

/-- A rational recomputation of the proved twelve-basis budget, including both
infinite tails. The table cannot supply J as an unchecked input. -/
def jBudget (p : WinnerHeightProfiles.Row) : ℚ :=
  let C := GaussianBasis.caps
  (1+1/10000)*(p.m1*C 0+p.m2*C 1+
    2*p.r0*(p.m1*C 2+p.m2*C 3)+p.r0^2*(p.m1*C 4+p.m2*C 5)+
    2/p.h*(p.m1*C 6+p.m2*C 7)+1/p.h^2*(p.m1*C 8+p.m2*C 9)+
    2*p.r0/p.h*(p.m1*C 10+p.m2*C 11))+
  (1+1/(1/10000))*p.r1^2*C 4+2/100000

theorem jBudget_cast (p : WinnerHeightProfiles.Row) :
    (jBudget p:ℝ) =
      (∑i : Fin 12, Gaussian.coefficient p.m1 p.m2 p.h p.r0 p.r1 (1/10000) 1 i *
        (GaussianBasis.caps i:ℝ))+2/100000 := by
  norm_num [jBudget,Gaussian.coefficient,GaussianBasis.caps,Fin.sum_univ_succ]
  push_cast
  ring

def Arithmetic (p : WinnerHeightProfiles.Row) (b : ℚ) : Prop :=
  0≤p.shift ∧ 0≤p.m1 ∧ p.m1≤129/200 ∧ 0≤p.m2 ∧ p.m2≤23/250 ∧ 28≤p.h ∧
  0≤p.r0 ∧ p.r0≤681/500000 ∧ 0≤p.r1 ∧ p.r1≤23/250000 ∧
  0<p.U ∧ 0<p.V ∧ 0<p.K ∧ 0<b ∧ b<6 ∧
  8*(601/5000)*(1000000000001/1000000000000)*(611/1000)^2*jBudget p≤p.U
deriving Decidable

def ScalarChecks (p : WinnerHeightProfiles.Row) (b : ℚ) : Prop :=
  CH2QRH.DensityComputation.checkUpperBound (oneExpr p) 0 0 p.m1 WinnerOriginalScalars.cfg=true ∧
  CH2QRH.DensityComputation.checkUpperBound (twoExpr p) 0 0 p.m2 WinnerOriginalScalars.cfg=true ∧
  checkFinSumLowerBoundFull (logExpr p) 0 0 p.h WinnerOriginalScalars.cfg=true ∧
  CH2QRH.DensityComputation.checkUpperBound (zeroExpr p) 0 0 p.r0 WinnerOriginalScalars.cfg=true ∧
  CH2QRH.DensityComputation.checkUpperBound (residualExpr p) 0 0 p.r1 WinnerOriginalScalars.cfg=true ∧
  CH2QRH.DensityComputation.checkUpperBound (vExpr p) 0 0 p.V WinnerOriginalScalars.cfg=true ∧
  CH2QRH.DensityComputation.checkUpperBound (kExpr p) 0 0 p.K WinnerOriginalScalars.cfg=true ∧
  checkFinSumLowerBoundFull (bExpr p) 0 0 b WinnerOriginalScalars.cfg=true
deriving Decidable

theorem shape_of_arithmetic (p : WinnerHeightProfiles.Row) (b : ℚ) (ha : Arithmetic p b) :
    Gaussian.Shape p.m1 p.m2 p.h p.r0 p.r1 := by
  rcases ha with ⟨_,hm1,hm1',hm2,hm2',hh,hr0,hr0',hr1,hr1',_⟩
  constructor
  · exact_mod_cast hm1
  · have hx : (p.m1:ℝ)≤((129/200:ℚ):ℝ) := by exact_mod_cast hm1'
    norm_num at hx
    exact hx
  · exact_mod_cast hm2
  · have hx : (p.m2:ℝ)≤((23/250:ℚ):ℝ) := by exact_mod_cast hm2'
    norm_num at hx
    exact hx
  · exact_mod_cast hh
  · exact_mod_cast hr0
  · have hx : (p.r0:ℝ)≤((681/500000:ℚ):ℝ) := by exact_mod_cast hr0'
    norm_num at hx
    exact hx
  · exact_mod_cast hr1
  · have hx : (p.r1:ℝ)≤((23/250000:ℚ):ℝ) := by exact_mod_cast hr1'
    norm_num at hx
    exact hx

/-- A genuine source kernel certificate: finite scalar checks and executed
universal quadrature feed the original actual source-moment interface. -/
noncomputable def kernelCertificate (p : WinnerHeightProfiles.Row) (b : ℚ)
    (ha : Arithmetic p b) (hc : ScalarChecks p b)
    (accepted : ∀j:Fin 18,WinnerProgramA.acceptUpper (GaussianBasis.output j)
      [(GaussianBasis.spec j).cap]=true) :
    WinnerNewHeightSource.KernelCertificate (anchor p) p.U where
  M1 := p.m1
  M2 := p.m2
  hbar := p.h
  r0 := p.r0
  r1 := p.r1
  J := jBudget p
  omegaBar := 1000000000001/1000000000000
  mean_one := by rw [←one_semantics];exact closed_upper _ _ hc.1
  mean_two := by rw [←two_semantics];exact closed_upper _ _ hc.2.1
  log_pos := by
    have hh : (28:ℝ)≤p.h := by exact_mod_cast ha.2.2.2.2.2.1
    linarith
  log_lower := by rw [←log_semantics];exact closed_lower _ _ hc.2.2.1
  ratio_zero := by rw [←zero_semantics];exact closed_upper _ _ hc.2.2.2.1
  ratio_one := by
    rw [←residual_semantics p (by exact_mod_cast ha.1)]
    exact closed_upper _ _ hc.2.2.2.2.1
  kernel_integrable := Gaussian.kernel_integrable (shape_of_arithmetic p b ha)
  kernel_budget := by
    rw [jBudget_cast]
    exact Gaussian.full_budget (shape_of_arithmetic p b ha) (by norm_num)
      (fun i => (GaussianBasis.caps i:ℝ)) (GaussianBasis.integral_caps accepted)
  omega_upper := omega_upper p (by exact_mod_cast ha.1)
  finite_U := by
    have hh : ((8*(601/5000)*(1000000000001/1000000000000)*(611/1000)^2*jBudget p:ℚ):ℝ)≤(p.U:ℝ) := by
      exact_mod_cast ha.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    norm_num at hh ⊢
    exact hh

#print axioms jBudget_cast
#print axioms kernelCertificate
end PVEvolutionA.Recovery.Profile
