/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitRHMellin
import ExplicitDerivativeIntegrals
import ExplicitRealZetaNonzero

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit

/-- Nonnegative actual multiplicity. On nontrivial zeros this is the order
of vanishing. Absolute value also makes all finite counting sums explicit. -/
def cmsMultiplicity (ρ : CMSZeroIndex) : ℝ := |(IEANTN.zetaOrder (ρ:ℂ):ℝ)|

/-- CMS Lemma 9 uses a RIGHT-CLOSED upper endpoint. The existing `zetaN`
vocabulary uses an open endpoint and is deliberately not substituted here. -/
def cmsCountFamily (T : ℝ) (ρ : CMSZeroIndex) : ℝ :=
  if 0 < (ρ:ℂ).im ∧ (ρ:ℂ).im ≤ T then cmsMultiplicity ρ else 0

def cmsPositiveZeroCount (T : ℝ) : ℝ := ∑' ρ : CMSZeroIndex, cmsCountFamily T ρ

def cmsQ (T : ℝ) : ℝ := T/(2*π)*log (T/(2*π*exp 1))+7/8

def cmsCountRemainder (T : ℝ) : ℝ := cmsPositiveZeroCount T-cmsQ T

/-- Literal general count input: CMS1708.04122v2 Lemma 9, Section 6.1,
printed p.23, including the separate N(10)=0 fact used in its proof.
Local summability prevents a totalized infinite-sum interpretation. -/
def SourceCMSZeroCounting : Prop :=
  (∀ T : ℝ, Summable (cmsCountFamily T)) ∧ cmsPositiveZeroCount 10 = 0 ∧
    ∀ T : ℝ, exp 1 ≤ T → |cmsCountRemainder T| ≤ (3/20:ℝ)*log T+3

/-- The source's selected root x0=9.676..., with its exact defining equation;
no arbitrary floating approximation is used as a root. This separate
literature input can be replaced by an elementary root-existence proof. -/
def SourceCMSZeroCountRoot : Prop :=
  ∃ T0 : ℝ, exp 1 ≤ T0 ∧ 9 < T0 ∧ T0 < 10 ∧ cmsQ T0 = 0

theorem cmsPositiveZeroCount_mono (hcount : SourceCMSZeroCounting) :
    Monotone cmsPositiveZeroCount := by
  intro a b hab
  apply Summable.tsum_le_tsum _ (hcount.1 a) (hcount.1 b)
  intro ρ
  unfold cmsCountFamily
  split_ifs with ha hb hb
  · rfl
  · exact False.elim (hb ⟨ha.1,ha.2.trans hab⟩)
  · exact abs_nonneg _
  · rfl

theorem cmsPositiveZeroCount_nonneg (T : ℝ) : 0 ≤ cmsPositiveZeroCount T := by
  apply tsum_nonneg
  intro ρ
  unfold cmsCountFamily cmsMultiplicity
  split_ifs <;> positivity

theorem cms_base_zero_of_le_ten (hcount : SourceCMSZeroCounting) (T0 : ℝ)
    (hT0 : T0 ≤ 10) : cmsPositiveZeroCount T0 = 0 := by
  have h := cmsPositiveZeroCount_mono hcount hT0
  rw [hcount.2.1] at h
  exact le_antisymm h (cmsPositiveZeroCount_nonneg T0)

/-- The two half-plane contributions are kept separate until the independently
proved absence of an ordinate-zero nontrivial zero is consumed. -/
def cmsSignedAmplitude (F : ℝ → ℝ) (Δ s : ℝ) (ρ : CMSZeroIndex) : ℝ :=
  if 0 < s*(ρ:ℂ).im then Δ*|F (Δ*(ρ:ℂ).im)| *cmsMultiplicity ρ else 0

def cmsAmplitude (F : ℝ → ℝ) (Δ : ℝ) (ρ : CMSZeroIndex) : ℝ :=
  Δ*|F (Δ*(ρ:ℂ).im)| *cmsMultiplicity ρ

def cmsZeroMain (F : ℝ → ℝ) (Δ T0 : ℝ) : ℝ :=
  ∫ u in Ioi (Δ*T0), log (u/(2*π*Δ))/(2*π)*|F u|

def cmsZeroRemainder (F' : ℝ → ℝ) (Δ T0 : ℝ) : ℝ :=
  ∫ u in Ioi (Δ*T0), ((3/20:ℝ)*log (u/Δ)+3)*|F' u|

/-- Explicit admissibility for the generic summation-by-parts proof scheme.
In particular both infinity boundary terms and both source integrals are
required; they cannot disappear into a window-specific numerical cap. -/
def CMSZeroAdmissible (F F' : ℝ → ℝ) (Δ T0 : ℝ) : Prop :=
  (∀ u : ℝ, HasDerivAt F (F' u) u) ∧ Continuous F' ∧ Function.Even F ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 1 ≤ |u| → |F u| ≤ C/u^2 ∧ |F' u| ≤ C/u^2) ∧
  IntegrableOn (fun u : ℝ => log (u/(2*π*Δ))/(2*π)*|F u|) (Ioi (Δ*T0)) ∧
  IntegrableOn (fun u : ℝ => ((3/20:ℝ)*log (u/Δ)+3)*|F' u|) (Ioi (Δ*T0)) ∧
  Tendsto (fun T : ℝ => Δ*|F (Δ*T)| *cmsQ T) atTop (𝓝 0) ∧
  Tendsto (fun T : ℝ => Δ*|F (Δ*T)| *cmsCountRemainder T) atTop (𝓝 0)

/-- General analytic source input reconstructed from CMS Section 6.1, the
summation-by-parts display between Lemma 9 and (6.9), with f(x)=Delta F(Delta x).
The section's worked function is particular; this is explicitly the GENERAL
PROOF-SCHEME SPECIALIZATION with all applicable hypotheses exposed, not a
claim that CMS prints a separately quantified theorem for every F.
The same display is stated for the negative ordinates in the following
paragraph. No affine window, support radius, numerical norm/moment, error
allowance or prime conclusion occurs in the proposition. The integration by
parts against the actual zero count remains a named source-backed input. -/
def SourceCMSZeroPartialSummationProofScheme : Prop :=
  SourceCMSZeroCounting → RiemannHypothesis →
  ∀ T0 : ℝ, exp 1 ≤ T0 → T0 < 10 → cmsQ T0 = 0 → cmsPositiveZeroCount T0 = 0 →
  ∀ F F' : ℝ → ℝ, ∀ Δ : ℝ, 0 < Δ → CMSZeroAdmissible F F' Δ T0 →
  ∀ s : ℝ, (s = 1 ∨ s = -1) →
    Summable (cmsSignedAmplitude F Δ s) ∧
    (∑' ρ : CMSZeroIndex, cmsSignedAmplitude F Δ s ρ) ≤
      cmsZeroMain F Δ T0+Δ*cmsZeroRemainder F' Δ T0

/-- The independent DLMF real-zeta integral input closes the ordinate-zero
case; it is not inferred from the positive-ordinate count N(10). -/
theorem cms_zero_im_ne_zero (hD : SourceDLMFRealEtaIntegral) (ρ : CMSZeroIndex) :
    (ρ:ℂ).im ≠ 0 := by
  intro him
  have heq : (ρ:ℂ) = (((ρ:ℂ).re:ℝ):ℂ) := by
    apply Complex.ext <;> simp [him]
  have hnonzero := real_zeta_ne_zero hD (ρ:ℂ).re ρ.property.1.1 ρ.property.1.2
  apply hnonzero
  rw [←heq]
  exact ρ.property.2.2

/-- Combining the two actual sign families consumes a separate proof that
there is no nontrivial zero with imaginary part zero. This prevents a hidden
loss of its contribution in the full Mellin spectral term. -/
theorem cms_full_zero_bound (hsource : SourceCMSZeroPartialSummationProofScheme)
    (hcount : SourceCMSZeroCounting) (hRH : RiemannHypothesis)
    (hnoReal : ∀ ρ : CMSZeroIndex, (ρ:ℂ).im ≠ 0)
    (T0 : ℝ) (hT0e : exp 1 ≤ T0) (hT010 : T0 < 10) (hQ : cmsQ T0 = 0)
    (F F' : ℝ → ℝ) (Δ : ℝ) (hΔ : 0 < Δ) (hadm : CMSZeroAdmissible F F' Δ T0) :
    Summable (cmsAmplitude F Δ) ∧
    (∑' ρ : CMSZeroIndex, cmsAmplitude F Δ ρ) ≤
      2*cmsZeroMain F Δ T0+2*Δ*cmsZeroRemainder F' Δ T0 := by
  have hb := cms_base_zero_of_le_ten hcount T0 hT010.le
  obtain ⟨hp,hpbound⟩ := hsource hcount hRH T0 hT0e hT010 hQ hb F F' Δ hΔ hadm 1 (Or.inl rfl)
  obtain ⟨hn,hnbound⟩ := hsource hcount hRH T0 hT0e hT010 hQ hb F F' Δ hΔ hadm (-1) (Or.inr rfl)
  have heq : cmsAmplitude F Δ = fun ρ => cmsSignedAmplitude F Δ 1 ρ+cmsSignedAmplitude F Δ (-1) ρ := by
    funext ρ
    rcases lt_or_gt_of_ne (hnoReal ρ) with hr|hr
    · simp [cmsAmplitude,cmsSignedAmplitude,show ¬0 < (ρ:ℂ).im by linarith,hr]
    · simp [cmsAmplitude,cmsSignedAmplitude,hr,show ¬0 < -(ρ:ℂ).im by linarith]
  rw [heq]
  refine ⟨hp.add hn,?_⟩
  rw [hp.tsum_add hn]
  linarith

/-- The full-zero theorem consumes the independent real-zeta nonvanishing
proof, so its ordinate-zero case is closed rather than silently discarded. -/
theorem cms_full_zero_bound_from_sources
    (hsource : SourceCMSZeroPartialSummationProofScheme)
    (hcount : SourceCMSZeroCounting) (hRH : RiemannHypothesis)
    (hD : SourceDLMFRealEtaIntegral)
    (T0 : ℝ) (hT0e : exp 1 ≤ T0) (hT010 : T0 < 10) (hQ : cmsQ T0 = 0)
    (F F' : ℝ → ℝ) (Δ : ℝ) (hΔ : 0 < Δ) (hadm : CMSZeroAdmissible F F' Δ T0) :
    Summable (cmsAmplitude F Δ) ∧
    (∑' ρ : CMSZeroIndex, cmsAmplitude F Δ ρ) ≤
      2*cmsZeroMain F Δ T0+2*Δ*cmsZeroRemainder F' Δ T0 :=
  cms_full_zero_bound hsource hcount hRH (cms_zero_im_ne_zero hD)
    T0 hT0e hT010 hQ F F' Δ hΔ hadm

#print axioms cms_full_zero_bound_from_sources
#print axioms cms_base_zero_of_le_ten
#print axioms cms_full_zero_bound
end RH080Next.Explicit
