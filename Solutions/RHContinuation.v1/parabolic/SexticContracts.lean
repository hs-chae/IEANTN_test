/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SexticWindow
import PsiSmoothing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Explicit analytic contracts for the written sextic RH theorem.
Each unproved contract names an actual weighted Mangoldt sum, actual zeta-zero
packet with multiplicity, or a scalar geometric assertion. No contract is the
prime-count conclusion. The consumer below compiles conditional on these exact
remaining obligations; it is not an end-to-end RH formalization. -/
namespace SexticWindow
open Real MeasureTheory Set Finset
noncomputable def D (L : ℝ) : ℝ := 1013 / 100 * L - 1
noncomputable def δ (L : ℝ) : ℝ := D L * Real.exp (-L / 2)
noncomputable def a (L : ℝ) : ℝ := Real.exp (L - δ L)
noncomputable def b (L : ℝ) : ℝ := Real.exp (L + δ L)
noncomputable def rawKernel (u : ℝ) : ℝ := 1 - u ^ 6
noncomputable def transform (y : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, rawKernel u * Real.cos (y * u)
noncomputable def zeroPacket (L : ℝ) (ρ : PsiSmoothing.Zero) : ℂ :=
  Complex.exp (Complex.I * ((ρ : ℂ).im * L : ℝ)) *
    (δ L * transform (δ L * (ρ : ℂ).im) : ℝ) *
    (IEANTN.zetaOrder ρ : ℂ)
noncomputable def zeroTerm (L : ℝ) : ℂ := ∑' ρ : PsiSmoothing.Zero, zeroPacket L ρ
noncomputable def mainTerm (L : ℝ) : ℝ :=
  D L * ∫ u in (-1 : ℝ)..1, rawKernel u * Real.cosh (δ L * u / 2)
noncomputable def trivialCost (L : ℝ) : ℝ :=
  ∫ t in a L..b L, window ((Real.log t - L) / δ L) /
    (Real.sqrt t * t * (t ^ 2 - 1))

/-- Distributional pairing of the integrated explicit formula; sum absolute
convergence and actual multiplicity are required. -/
def SexticExplicitFormula : Prop :=
  RiemannHypothesis → ∀ L : ℝ, 24 ≤ L →
    Summable (zeroPacket L) ∧
    mangoldtWeighted (a L) (b L) L (δ L) =
      mainTerm L - (zeroTerm L).re - trivialCost L

/-- Whole-zero observable derived by Stieltjes integration from the count theorem
and the actual continuous Fourier mass/log-moment enclosures. -/
def SexticZeroEstimate : Prop :=
  RiemannHypothesis → ∀ L : ℝ, 24 ≤ L →
    ‖zeroTerm L‖ ≤ 172 / 100 * (L / 2 - Real.log (2 * Real.pi * D L)) +
      13 / 10 + 17 / 1000

/-- Actual positive prime-power correction, not an assumed ordinary-prime count. -/
def SexticPrimePowerCost : Prop :=
  ∀ L : ℝ, 24 ≤ L →
    mangoldtWeighted (a L) (b L) L (δ L) -
      primeWeighted (a L) (b L) L (δ L) ≤ 155 / 10000

def SexticTrivialCost : Prop := ∀ L : ℝ, 24 ≤ L → trivialCost L ≤ 1 / 1000

/-- These are scalar endpoint/monotonicity obligations, proved in the written
whole-ray proof and exact endpoint script; not yet all proved in Lean. -/
def SexticScalarGeometry : Prop := ∀ L : ℝ, 24 ≤ L →
  0 < a L ∧ 2 ≤ Real.log (a L) ∧ a L ≤ b L ∧
  L - δ L = Real.log (a L) ∧ 0 ≤ δ L ∧
  212 / 7 < 172 / 100 * Real.log (2 * Real.pi * D L) - (12 / 7 + 13 / 10 + 34 / 1000)

/-- Continuous monotone change of center plus the proved strict width estimate.
This geometric condition has no prime, psi or zero quantity in it. -/
def SexticForwardCoverage : Prop := ∀ u : ℝ, Real.exp 24 ≤ u →
  ∃ L : ℝ, 24 ≤ L ∧ a L = u ∧
    b L ≤ u + 109 / 50 * Real.sqrt u * Real.log u

theorem rawKernel_nonneg {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ rawKernel u := by
  have h := mul_nonpos_of_nonneg_of_nonpos (by linarith [hu.1] : 0 ≤ u + 1)
    (by linarith [hu.2] : u - 1 ≤ 0)
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  have hprod := mul_nonneg (by linarith : 0 ≤ 1 - u ^ 2)
    (by positivity : 0 ≤ 1 + u ^ 2 + u ^ 4)
  unfold rawKernel
  nlinarith

theorem rawKernel_mass : (∫ u in (-1 : ℝ)..1, rawKernel u) = 12 / 7 := by
  unfold rawKernel
  rw [intervalIntegral.integral_sub]
  · rw [integral_pow]
    norm_num
  · exact intervalIntegrable_const
  · exact (continuous_id.pow 6).intervalIntegrable (-1) 1

theorem mainTerm_lower {L : ℝ} (hL : 24 ≤ L) : 12 / 7 * D L ≤ mainTerm L := by
  have hd : 0 ≤ D L := by unfold D; linarith
  have hk : Continuous rawKernel := by unfold rawKernel; fun_prop
  have hkc : Continuous (fun u : ℝ => rawKernel u * Real.cosh (δ L * u / 2)) := by
    unfold rawKernel
    fun_prop
  have hi : (∫ u in (-1 : ℝ)..1, rawKernel u) ≤
      ∫ u in (-1 : ℝ)..1, rawKernel u * Real.cosh (δ L * u / 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hk.intervalIntegrable (-1) 1) (hkc.intervalIntegrable (-1) 1)
    intro u hu
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.one_le_cosh _) (rawKernel_nonneg hu)
  rw [rawKernel_mass] at hi
  unfold mainTerm
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi hd

/-- The actual weighted-prime lower bound is derived from separate analytic
observables and actual prime-power cost, rather than assumed as the count target. -/
theorem weighted_from_components (rh : RiemannHypothesis)
    (hef : SexticExplicitFormula) (hz : SexticZeroEstimate)
    (hpp : SexticPrimePowerCost) (ht : SexticTrivialCost)
    (hg : SexticScalarGeometry) {L : ℝ} (hL : 24 ≤ L) :
    353 / 350 * L + 212 / 7 < primeWeighted (a L) (b L) L (δ L) := by
  have heq := (hef rh L hL).2
  have hzero := (Complex.abs_re_le_norm (zeroTerm L)).trans (hz rh L hL)
  have hre : (zeroTerm L).re ≤
      172 / 100 * (L / 2 - Real.log (2 * Real.pi * D L)) + 13 / 10 + 17 / 1000 :=
    (le_abs_self _).trans hzero
  have hm := mainTerm_lower hL
  have hp := hpp L hL
  have htr := ht L hL
  have hmargin := (hg L hL).2.2.2.2.2
  unfold D at hm
  linarith

/-- Actual ordinary prime-count difference for every eligible real lower endpoint.
The listed exact analytic and geometric obligations remain visible parameters. -/
theorem prime_count_218 (rh : RiemannHypothesis)
    (hef : SexticExplicitFormula) (hz : SexticZeroEstimate)
    (hpp : SexticPrimePowerCost) (ht : SexticTrivialCost)
    (hg : SexticScalarGeometry) (hc : SexticForwardCoverage) :
    ∀ u : ℝ, Real.exp 24 ≤ u →
      (353 / 350 + (212 / 7) / Real.log u) * Real.sqrt u <
        primeCounting (u + 109 / 50 * Real.sqrt u * Real.log u) - primeCounting u := by
  intro u hu
  obtain ⟨L, hL, hcenter, hwidth⟩ := hc u hu
  obtain ⟨ha, hla, hab, hlog, hδ, hmargin⟩ := hg L hL
  have hweighted := weighted_from_components rh hef hz hpp ht hg hL
  have hcnt := prime_count_from_weighted ha hla hab hlog
    (by norm_num : (0 : ℝ) < 212 / 7) (by norm_num : (0 : ℝ) ≤ 353 / 350)
    hδ hweighted
  have hmono : primeCounting (b L) ≤
      primeCounting (u + 109 / 50 * Real.sqrt u * Real.log u) := by
    unfold primeCounting
    exact_mod_cast Nat.monotone_primeCounting (Nat.floor_le_floor hwidth)
  rw [hcenter] at hcnt
  linarith

#print axioms prime_count_218
#print axioms weighted_from_components
end SexticWindow
