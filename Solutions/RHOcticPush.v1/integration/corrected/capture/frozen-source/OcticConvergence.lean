import OcticDecay
import NicolasSpectralMass
import Section6Zeros

/-! Full actual-zero convergence from the existing exact Nicolas source.
This does not prove the sharp 1.822 logarithmic estimate or the explicit formula.
Every zero and its multiplicity is transported, with no finite-height substitution. -/
namespace RHOcticPush.Convergence
open Real Complex Set
set_option maxHeartbeats 0

def zeroEquiv : PsiSmoothing.Zero ≃ RHLimit.NicolasMass.Zero where
  toFun z := ⟨z.val, z.property.1.1, z.property.1.2, z.property.2.2⟩
  invFun z := ⟨z.val, ⟨z.property.1, z.property.2.1⟩, Set.mem_univ _, z.property.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

lemma order_nonneg (z : PsiSmoothing.Zero) : 0 ≤ IEANTN.zetaOrder z := by
  apply CH2Section6.zetaOrder_nonneg_of_ne_one
  intro h
  have hr := congrArg Complex.re h
  have hz := z.property.1.2
  norm_num at hr
  linarith

lemma multiplicity_eq (z : PsiSmoothing.Zero) :
    (NicolasContinuation.multiplicity (zeroEquiv z) : ℤ) = IEANTN.zetaOrder z := by
  exact Int.toNat_of_nonneg (order_nonneg z)

noncomputable def weight (z : PsiSmoothing.Zero) : ℝ :=
  RHLimit.NicolasMass.weight (zeroEquiv z)

lemma weight_eq (rh : RiemannHypothesis) (z : PsiSmoothing.Zero) :
    weight z = (IEANTN.zetaOrder z : ℝ) / (1 / 4 + z.val.im ^ 2) := by
  have hr := RHLimit.NicolasMass.zero_re rh (zeroEquiv z)
  have hm : (NicolasContinuation.multiplicity (zeroEquiv z) : ℝ) =
      (IEANTN.zetaOrder z : ℝ) := by exact_mod_cast multiplicity_eq z
  unfold weight RHLimit.NicolasMass.weight
  rw [hm, Complex.sq_norm, Complex.normSq_apply]
  change _ / (z.val.re * z.val.re + z.val.im * z.val.im) = _
  change z.val.re = 1 / 2 at hr
  rw [hr]
  congr 1
  ring

theorem weight_summable (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) : Summable weight := by
  exact zeroEquiv.summable_iff.mpr (RHLimit.NicolasMass.weight_summable rh hN)

theorem weight_mass_le_beta (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) :
    (∑' z : PsiSmoothing.Zero, weight z) ≤ NicolasContinuation.beta := by
  simp only [weight]
  rw [zeroEquiv.tsum_eq]
  exact RHLimit.NicolasMass.mass_le_beta rh hN

noncomputable def envelope (δ : ℝ) : ℝ := 32 / δ + 4 * δ / 9

lemma envelope_pos {δ : ℝ} (hδ : 0 < δ) : 0 < envelope δ := by
  unfold envelope
  positivity

theorem scaled_transform_majorant {δ γ : ℝ} (hδ : 0 < δ) :
    δ * |EvenKernel.transform 4 (δ * γ)| ≤ envelope δ / (1 / 4 + γ ^ 2) := by
  have h0 := RHOcticPush.Decay.transform_abs_le_mass 4 (δ * γ)
  norm_num [EvenKernel.mass] at h0
  have h2 := RHOcticPush.Decay.transform_quadratic_decay (δ * γ)
  have hd0 : 0 < (1 / 4 : ℝ) + γ ^ 2 := by positivity
  have hw : δ ^ 2 * |EvenKernel.transform 4 (δ * γ)| * (1 / 4 + γ ^ 2) ≤
      32 + 4 * δ ^ 2 / 9 := by
    nlinarith [mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr h0)]
  have hh : δ * |EvenKernel.transform 4 (δ * γ)| * (1 / 4 + γ ^ 2) ≤
      (32 + 4 * δ ^ 2 / 9) / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith [hw]
  have he : (32 + 4 * δ ^ 2 / 9) / δ = envelope δ := by
    unfold envelope
    field_simp
  rw [he] at hh
  exact (le_div_iff₀ hd0).mpr hh

lemma packet_norm {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) (z : PsiSmoothing.Zero) :
    ‖EvenKernel.zeroPacket 4 C L z‖ =
      EvenKernel.δ C L * |EvenKernel.transform 4 (EvenKernel.δ C L * z.val.im)| *
        (IEANTN.zetaOrder z : ℝ) := by
  have ho : (0 : ℝ) ≤ IEANTN.zetaOrder z := by exact_mod_cast order_nonneg z
  have he : ‖Complex.exp (Complex.I * (z.val.im * L : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hc : (IEANTN.zetaOrder z : ℂ) = ((IEANTN.zetaOrder z : ℝ) : ℂ) := by norm_cast
  unfold EvenKernel.zeroPacket
  rw [norm_mul, norm_mul, he, hc, Complex.norm_real, Complex.norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hδ, abs_of_nonneg ho]
  ring

theorem packet_norm_majorant (rh : RiemannHypothesis) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) (z : PsiSmoothing.Zero) :
    ‖EvenKernel.zeroPacket 4 C L z‖ ≤ envelope (EvenKernel.δ C L) * weight z := by
  rw [packet_norm hδ z, weight_eq rh z]
  have ho : (0 : ℝ) ≤ IEANTN.zetaOrder z := by exact_mod_cast order_nonneg z
  calc
    _ ≤ envelope (EvenKernel.δ C L) / (1 / 4 + z.val.im ^ 2) *
        (IEANTN.zetaOrder z : ℝ) :=
      mul_le_mul_of_nonneg_right (scaled_transform_majorant hδ) ho
    _ = _ := by ring

/-- Absolute summability of the original full zero family, not merely a finite truncation. -/
theorem packet_norm_summable (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) :
    Summable (fun z : PsiSmoothing.Zero => ‖EvenKernel.zeroPacket 4 C L z‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (packet_norm_majorant rh hδ)
  exact (weight_summable rh hN).mul_left _

theorem packet_summable (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) : Summable (EvenKernel.zeroPacket 4 C L) :=
  (packet_norm_summable rh hN hδ).of_norm

/-- A complete, deliberately coarse infinite-zero bound. It is NOT the sharp
1.822 logarithmic target, and its extra named Nicolas input is explicit. -/
theorem full_zero_coarse_bound (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) :
    ‖EvenKernel.zeroTerm 4 C L‖ ≤ envelope (EvenKernel.δ C L) * NicolasContinuation.beta := by
  have hs := weight_summable rh hN
  have hsum : ‖EvenKernel.zeroTerm 4 C L‖ ≤
      ∑' z : PsiSmoothing.Zero, envelope (EvenKernel.δ C L) * weight z :=
    tsum_of_norm_bounded (hs.mul_left _).hasSum (packet_norm_majorant rh hδ)
  rw [tsum_mul_left] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left (weight_mass_le_beta rh hN)
    (envelope_pos hδ).le)

/-- Any independently justified finite collection of actual zeros can be used
without discarding the remaining infinite family. This is a genuine remainder
bound, with the unused inverse-square mass subtracted rather than reset to beta. -/
theorem finite_packet_remainder (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) (s : Finset PsiSmoothing.Zero) :
    ‖EvenKernel.zeroTerm 4 C L - ∑ z ∈ s, EvenKernel.zeroPacket 4 C L z‖ ≤
      envelope (EvenKernel.δ C L) *
        (NicolasContinuation.beta - ∑ z ∈ s, weight z) := by
  classical
  have hs := weight_summable rh hN
  have hp := (packet_summable rh hN hδ).sum_add_tsum_subtype_compl s
  have he : EvenKernel.zeroTerm 4 C L - ∑ z ∈ s, EvenKernel.zeroPacket 4 C L z =
      ∑' z : {z : PsiSmoothing.Zero // z ∉ s}, EvenKernel.zeroPacket 4 C L z := by
    unfold EvenKernel.zeroTerm
    rw [← hp]
    abel
  rw [he]
  have ht : ‖∑' z : {z : PsiSmoothing.Zero // z ∉ s}, EvenKernel.zeroPacket 4 C L z‖ ≤
      ∑' z : {z : PsiSmoothing.Zero // z ∉ s}, envelope (EvenKernel.δ C L) * weight z :=
    tsum_of_norm_bounded ((hs.subtype (fun z => z ∉ s)).mul_left _).hasSum
      (fun z => packet_norm_majorant rh hδ z)
  rw [tsum_mul_left] at ht
  have hw := hs.sum_add_tsum_subtype_compl s
  have hm := weight_mass_le_beta rh hN
  have hc : (∑' z : {z : PsiSmoothing.Zero // z ∉ s}, weight z) ≤
      NicolasContinuation.beta - ∑ z ∈ s, weight z := by linarith
  exact ht.trans (mul_le_mul_of_nonneg_left hc (envelope_pos hδ).le)

/-- Actual finite partial sums tend to the actual complete zero sum. -/
theorem finite_packet_remainder_tends_zero (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) :
    Filter.Tendsto
      (fun s : Finset PsiSmoothing.Zero =>
        EvenKernel.zeroTerm 4 C L - ∑ z ∈ s, EvenKernel.zeroPacket 4 C L z)
      Filter.atTop (nhds 0) := by
  have hp := (packet_summable rh hN hδ).hasSum
  have hc : Filter.Tendsto
      (fun _ : Finset PsiSmoothing.Zero => EvenKernel.zeroTerm 4 C L)
      Filter.atTop (nhds (EvenKernel.zeroTerm 4 C L)) := tendsto_const_nhds
  simpa only [EvenKernel.zeroTerm, sub_self] using
    (hc.sub hp)

theorem packet_summable_on_full_parameter_ray (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) {C L : ℝ}
    (hC : 103 / 100 ≤ C) (hL : 24 ≤ L) :
    Summable (EvenKernel.zeroPacket 4 C L) := by
  apply packet_summable rh hN
  have hd : 0 < EvenKernel.D C L := by
    unfold EvenKernel.D
    nlinarith
  exact mul_pos hd (Real.exp_pos _)

#print axioms multiplicity_eq
#print axioms packet_summable
#print axioms full_zero_coarse_bound
#print axioms finite_packet_remainder
#print axioms finite_packet_remainder_tends_zero
#print axioms packet_summable_on_full_parameter_ray
end RHOcticPush.Convergence
