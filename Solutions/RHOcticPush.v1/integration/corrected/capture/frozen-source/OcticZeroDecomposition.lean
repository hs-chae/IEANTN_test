import OcticGreenSource
import Section6Res

/-! A literal multiplicity-preserving decomposition of all proper zeta zeros
under RH. In particular, the source's all-zero sum is not silently changed to a
critical-strip sum, and the simple trivial-zero theorem is reused from CH2. -/
namespace RHOcticPush.ZeroDecomposition
open Complex
open RHOcticPush.GreenSource
set_option maxHeartbeats 0

def properOfStrip (z : PsiSmoothing.Zero) : ProperZero :=
  ⟨z.val, by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith [z.property.1.2], z.property.2.2⟩

def trivialZero (n : ℕ) : ProperZero :=
  ⟨-2 * ((n : ℂ) + 1), by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    nlinarith [Nat.cast_nonneg (α := ℝ) n], riemannZeta_neg_two_mul_nat_add_one n⟩

def encode : PsiSmoothing.Zero ⊕ ℕ → ProperZero := Sum.elim properOfStrip trivialZero

theorem encode_injective : Function.Injective encode := by
  intro x y h
  cases x with
  | inl z =>
    cases y with
    | inl w =>
      have hv := congrArg (fun u : ProperZero => u.val) h
      change z.val = w.val at hv
      exact congrArg Sum.inl (Subtype.ext hv)
    | inr n =>
      have hv := congrArg (fun u : ProperZero => u.val.re) h
      change z.val.re = (-2 * ((n : ℂ) + 1)).re at hv
      norm_num at hv
      have hp := z.property.1.1
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  | inr n =>
    cases y with
    | inl z =>
      have hv := congrArg (fun u : ProperZero => u.val.re) h
      change (-2 * ((n : ℂ) + 1)).re = z.val.re at hv
      norm_num at hv
      have hp := z.property.1.1
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    | inr m =>
      have hv := congrArg (fun u : ProperZero => u.val.re) h
      change (-2 * ((n : ℂ) + 1)).re = (-2 * ((m : ℂ) + 1)).re at hv
      norm_num at hv
      exact congrArg Sum.inr hv

theorem encode_surjective (rh : RiemannHypothesis) : Function.Surjective encode := by
  intro z
  by_cases ht : ∃ n : ℕ, z.val = -2 * ((n : ℂ) + 1)
  · obtain ⟨n, hn⟩ := ht
    exact ⟨Sum.inr n, Subtype.ext hn.symm⟩
  · have hr := rh z.val z.property.2 ht z.property.1
    let w : PsiSmoothing.Zero :=
      ⟨z.val, ⟨by rw [hr]; norm_num, by rw [hr]; norm_num⟩, Set.mem_univ _, z.property.2⟩
    exact ⟨Sum.inl w, Subtype.ext rfl⟩

noncomputable def decomposition (rh : RiemannHypothesis) :
    (PsiSmoothing.Zero ⊕ ℕ) ≃ ProperZero :=
  Equiv.ofBijective encode ⟨encode_injective, encode_surjective rh⟩

theorem trivial_multiplicity (n : ℕ) : IEANTN.zetaOrder (trivialZero n).val = 1 :=
  CH2Section6.zetaOrder_trivial n

theorem strip_multiplicity (z : PsiSmoothing.Zero) :
    IEANTN.zetaOrder (properOfStrip z).val = IEANTN.zetaOrder z.val := rfl

/-- Actual splitting of a summable source family. The summability premise is
essential: an arbitrary totalized tsum cannot be partitioned this way. -/
theorem all_zero_sum (rh : RiemannHypothesis) (f : ProperZero → ℂ) (hf : Summable f) :
    (∑' z : ProperZero, f z) =
      (∑' z : PsiSmoothing.Zero, f (properOfStrip z)) +
        ∑' n : ℕ, f (trivialZero n) := by
  have hs : Summable (fun z : PsiSmoothing.Zero ⊕ ℕ => f (encode z)) :=
    (decomposition rh).summable_iff.mpr hf
  rw [← (decomposition rh).tsum_eq f]
  exact Summable.tsum_sum (hs.comp_injective Sum.inl_injective)
    (hs.comp_injective Sum.inr_injective)

#print axioms encode_surjective
#print axioms trivial_multiplicity
#print axioms all_zero_sum
end RHOcticPush.ZeroDecomposition
