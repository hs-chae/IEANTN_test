import ExplicitCMSConjugationOrder
import ExplicitCMSZeroSource
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Complex Filter Set
open scoped Topology ComplexConjugate
namespace RH080Next.Explicit.CMSConjugation

theorem zetaOrder_conj (z : ℂ) : IEANTN.zetaOrder (conj z)=IEANTN.zetaOrder z := by
  unfold IEANTN.zetaOrder
  rw [riemannZeta_order_conj]

/-- Conjugation maps the actual nontrivial zeta-zero subtype to itself. -/
def zeroConj (ρ : CMSZeroIndex) : CMSZeroIndex :=
  ⟨conj (ρ:ℂ),by
    change (conj (ρ:ℂ)).re ∈ Ioo (0:ℝ) 1 ∧ (conj (ρ:ℂ)).im ∈ (univ : Set ℝ) ∧ riemannZeta (conj (ρ:ℂ))=0
    refine ⟨by simpa only [Complex.conj_re] using ρ.property.1,by trivial,?_⟩
    rw [riemannZeta_conj,ρ.property.2.2,map_zero]⟩

@[simp] theorem zeroConj_coe (ρ : CMSZeroIndex) : (zeroConj ρ : ℂ)=conj (ρ:ℂ) := rfl

@[simp] theorem zeroConj_involutive (ρ : CMSZeroIndex) : zeroConj (zeroConj ρ)=ρ := by
  apply Subtype.ext
  exact Complex.conj_conj (ρ:ℂ)

def zeroConjEquiv : CMSZeroIndex ≃ CMSZeroIndex :=
  ⟨zeroConj,zeroConj,zeroConj_involutive,zeroConj_involutive⟩

@[simp] theorem multiplicity_conj (ρ : CMSZeroIndex) : cmsMultiplicity (zeroConj ρ)=cmsMultiplicity ρ := by
  unfold cmsMultiplicity
  rw [zeroConj_coe,zetaOrder_conj]

/-- The actual negative-ordinate summand is the positive-ordinate summand at
the conjugate zero, with its actual meromorphic-order multiplicity. -/
theorem signed_amplitude_conj {F : ℝ → ℝ} (even : Function.Even F) (Δ : ℝ) (ρ : CMSZeroIndex) :
    cmsSignedAmplitude F Δ 1 (zeroConj ρ)=cmsSignedAmplitude F Δ (-1) ρ := by
  simp only [cmsSignedAmplitude,zeroConj_coe,Complex.conj_im,one_mul,neg_one_mul,
    mul_neg,multiplicity_conj]
  rw [even (Δ*(ρ:ℂ).im)]

/-- The negative half-plane family is summable and its actual total equals
the positive family's total. Reindexing uses the actual zero subtype and
proved zeta multiplicity symmetry, with no zero-pairing/source premise. -/
theorem negative_of_positive {F : ℝ → ℝ} (even : Function.Even F) (Δ : ℝ)
    (positive : Summable (cmsSignedAmplitude F Δ 1)) :
    Summable (cmsSignedAmplitude F Δ (-1)) ∧
      (∑'ρ : CMSZeroIndex,cmsSignedAmplitude F Δ (-1) ρ)=
        ∑'ρ : CMSZeroIndex,cmsSignedAmplitude F Δ 1 ρ := by
  have reindexed : cmsSignedAmplitude F Δ 1 ∘ zeroConjEquiv=cmsSignedAmplitude F Δ (-1) := by
    funext ρ
    exact signed_amplitude_conj even Δ ρ
  refine ⟨?_,?_⟩
  · rw [←reindexed]
    exact zeroConjEquiv.summable_iff.mpr positive
  · rw [←reindexed]
    exact zeroConjEquiv.tsum_eq (cmsSignedAmplitude F Δ 1)

#print axioms zetaOrder_conj
#print axioms multiplicity_conj
#print axioms negative_of_positive
end RH080Next.Explicit.CMSConjugation
