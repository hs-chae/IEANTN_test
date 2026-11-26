/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitNormSourceBridge
import IEANTN.Vocabulary.CMSFunctional
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit

def brDenominatorFour (nodes : List ℚ) (m : ℕ) : ℝ :=
  inverseCosine (affineSpectrum nodes m) 0 -
    4*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)
def brAmplitudeMass (nodes : List ℚ) (m : ℕ) : ℝ :=
  ∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|
def brQ1Error (x : ℝ) : ℝ := log (log x)/log x+2*(log x/sqrt x)

/-- Source input: BR v2 Proposition prop:uniform, equation eq:uniform-count,
restricted to Q(x)={1}. Then eta=log(x)/sqrt(x), phi(1)=1. The proof's
q=1 principal conductor-one case and following "The moduli1and2" paragraph
explicitly require only RH. M is certified to be the actual attained sup norm.
The source O(F,c) remainder is represented by an eventual C>=0 bound, not
silently discarded. This is a general literature proposition, not a proved
source theorem or a fixed-window/final-numerical conclusion. -/
def SourceBRUniformPopulationQ1 : Prop :=
  ∀ nodes : List ℚ, ∀ m : ℕ, 0 < m → nodes.length = 5*m+1 →
    node nodes (5*m) = 0 → ∀ M : ℝ, 0 < M →
    (∀ v : ℝ, |affineSpectrum nodes m v| ≤ M) →
    (∃ v : ℝ, |affineSpectrum nodes m v| = M) →
    0 < brDenominatorFour nodes m → ∀ c : ℝ, 0 < c → RiemannHypothesis →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      (c*brDenominatorFour nodes m-brAmplitudeMass nodes m)/(2*M)-C*brQ1Error x ≤
        IEANTN.CMSFunctional.normalizedPopulation c x

theorem brQ1Error_tendsto_zero : Tendsto brQ1Error atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => log x/x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hll := hlog.comp Real.tendsto_log_atTop
  have hls : Tendsto (fun x : ℝ => log x/sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  change Tendsto (fun x : ℝ => log (log x)/log x+2*(log x/sqrt x)) atTop (𝓝 0)
  simpa only [Function.comp_def,mul_zero,add_zero] using hll.add (hls.const_mul 2)

/-- Full actual-pi eventual consumer. The published remainder is discharged
by its proved limit; no old finite onset is claimed. Padding is exact, so the
source class applies to any shorter affine witness without changing it. -/
theorem source_BR_population_goodCoefficient (hsource : SourceBRUniformPopulationQ1)
    (nodes : List ℚ) (m : ℕ) (hm : 0 < m) (hlen : 2 ≤ nodes.length)
    (hlen5 : nodes.length ≤ 5*m+1) (hlast : node nodes (nodes.length-1) = 0)
    (M : ℝ) (hM : 0 < M) (hbound : ∀ v : ℝ, |affineSpectrum nodes m v| ≤ M)
    (hattain : ∃ v : ℝ, |affineSpectrum nodes m v| = M)
    (hD : 0 < brDenominatorFour nodes m) (c α : ℝ) (hc : 0 < c)
    (hbase : α < (c*brDenominatorFour nodes m-brAmplitudeMass nodes m)/(2*M))
    (hRH : RiemannHypothesis) : IEANTN.CMSFunctional.GoodCoefficient α c := by
  let k := 5*m+1-nodes.length
  let padded := nodes ++ List.replicate k 0
  have hplen : padded.length = 5*m+1 := by simp [padded,k]; omega
  have hplast : node padded (5*m) = 0 := by
    dsimp [padded]
    rw [node_append_zeros]
    by_cases heq : 5*m = nodes.length-1
    · rw [heq,hlast]
    · unfold node
      rw [List.getD_eq_default _ _ (by omega)]
      norm_num
  have hW : affineSpectrum padded m = affineSpectrum nodes m :=
    affineSpectrum_append_zeros nodes k m hlen hlast
  have hDp : brDenominatorFour padded m = brDenominatorFour nodes m := by
    unfold brDenominatorFour
    rw [hW]
  have hNp : brAmplitudeMass padded m = brAmplitudeMass nodes m := by
    unfold brAmplitudeMass
    rw [hW]
  obtain ⟨C,hC,hLower⟩ := hsource padded m hm hplen hplast M hM
    (by simpa only [hW] using hbound) (by simpa only [hW] using hattain)
    (by simpa only [hDp] using hD) c hc hRH
  rw [hDp,hNp] at hLower
  let δ : ℝ := ((c*brDenominatorFour nodes m-brAmplitudeMass nodes m)/(2*M)-α)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hErr : Tendsto (fun x : ℝ => C*brQ1Error x) atTop (𝓝 0) := by
    simpa only [mul_zero] using brQ1Error_tendsto_zero.const_mul C
  have hSmall : ∀ᶠ x : ℝ in atTop, C*brQ1Error x < δ :=
    (tendsto_order.1 hErr).2 δ hδ
  refine ⟨hc,δ,hδ,?_⟩
  filter_upwards [hLower,hSmall] with x hx hs
  dsimp [δ] at *
  linarith

/-- The peak node is the actual value of the affine window at zero. -/
theorem affineSpectrum_zero (nodes : List ℚ) (m : ℕ) :
    affineSpectrum nodes m 0 = node nodes 0 := by
  unfold affineSpectrum
  simp only [mul_zero,zero_sub,zero_add]
  rw [show hat 0 = 1 by norm_num [hat],mul_one]
  have hs : (∑ j ∈ Finset.Ico 1 (nodes.length-1), node nodes j*(hat (-(j:ℝ))+hat (j:ℝ))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hj).1
    have hjabs : |(j:ℝ)| = (j:ℝ) := abs_of_nonneg (Nat.cast_nonneg j)
    have hz : hat (j:ℝ) = 0 := hat_eq_zero _ (by rw [hjabs]; exact hj1)
    simp [hat_neg,hz]
  rw [hs,add_zero]

end RH080Next.Explicit
