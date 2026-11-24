import OcticBPTSpecialization
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! Conjugate pairing and the exact low-height exclusion on the actual zero family.
BPT and Nicolas remain explicit, independent literature inputs. -/
namespace RHOcticPush.ZeroPairing
open Real Complex Set MeasureTheory
open RHOcticPush.Convergence RHOcticPush.BPTSpecialization
set_option maxHeartbeats 0

lemma beta_lt_four : NicolasContinuation.beta < (4 : ℝ) := by
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold NicolasContinuation.beta
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

lemma order_zero_on_real_axis (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (z : PsiSmoothing.Zero)
    (hz : z.val.im = 0) : IEANTN.zetaOrder z.val = 0 := by
  have hs := weight_summable rh hN
  have hzle := hs.le_tsum z (fun v _ => RHLimit.NicolasMass.weight_nonneg (zeroEquiv v))
  have hm := weight_mass_le_beta rh hN
  rw [weight_eq rh z, hz] at hzle
  have hint : (IEANTN.zetaOrder z.val : ℝ) < 1 := by
    norm_num at hzle
    linarith [beta_lt_four]
  have hn : IEANTN.zetaOrder z.val < 1 := by exact_mod_cast hint
  exact le_antisymm (by omega) (order_nonneg z)

lemma order_zero_low_positive (hB : RHLimit.BPTZeroCount.PublishedBound) {z : ℂ}
    (hz : riemannZeta z = 0) (hpos : 0 < z.im) (hsmall : z.im ≤ 12) :
    IEANTN.zetaOrder z = 0 := by
  classical
  let T := (CH2Section7Z.finite_zeros_Ioc (a := 0) (b := 12) le_rfl).toFinset
  have hmem : z ∈ T := (Set.Finite.mem_toFinset _).mpr
    ⟨mem_univ _, ⟨hpos, hsmall⟩, hz⟩
  have hle : (IEANTN.zetaOrder z : ℝ) ≤ ∑ v ∈ T, (IEANTN.zetaOrder v : ℝ) := by
    apply Finset.single_le_sum _ hmem
    intro v hv
    exact CH2Section7Z.zetaOrder_nonneg_of_mem Ioc_subset_Ioi_self
      ((Set.Finite.mem_toFinset _).mp hv)
  have hcount := RHLimit.BPTZeroCount.count_twelve_zero hB
  unfold ZeroCount.v1.zetaNClosed at hcount
  rw [CH2Section7Z.zetaZeroesSum_eq_sum
    (CH2Section7Z.finite_zeros_Ioc (a := 0) (b := 12) le_rfl)] at hcount
  simp only [one_mul] at hcount
  change (∑ v ∈ T, (IEANTN.zetaOrder v : ℝ)) = 0 at hcount
  have hnonneg : (0 : ℝ) ≤ IEANTN.zetaOrder z :=
    CH2Section7Z.zetaOrder_nonneg_of_mem Ioc_subset_Ioi_self
      ((Set.Finite.mem_toFinset _).mp hmem)
  have : (IEANTN.zetaOrder z : ℝ) = 0 := by linarith
  exact_mod_cast this

def conjugate : PsiSmoothing.Zero ≃ PsiSmoothing.Zero where
  toFun z := ⟨starRingEnd ℂ z.val,
    (by simpa only [Complex.conj_re] using z.property.1), mem_univ _,
    (by change riemannZeta (starRingEnd ℂ z.val) = 0
        rw [riemannZeta_conj, z.property.2.2, map_zero])⟩
  invFun z := ⟨starRingEnd ℂ z.val,
    (by simpa only [Complex.conj_re] using z.property.1), mem_univ _,
    (by change riemannZeta (starRingEnd ℂ z.val) = 0
        rw [riemannZeta_conj, z.property.2.2, map_zero])⟩
  left_inv z := Subtype.ext (Complex.conj_conj _)
  right_inv z := Subtype.ext (Complex.conj_conj _)

lemma order_zero_low (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound) (z : PsiSmoothing.Zero)
    (hz : |z.val.im| ≤ 12) : IEANTN.zetaOrder z.val = 0 := by
  rcases lt_trichotomy z.val.im 0 with hn | he | hp
  · have hc := order_zero_low_positive hB
      (z := starRingEnd ℂ z.val)
      (by rw [riemannZeta_conj, z.property.2.2, map_zero])
      (by simpa using neg_pos.mpr hn)
      (by simp only [Complex.conj_im]; linarith [(abs_le.mp hz).1])
    rwa [CH2Section6.zetaOrder_conj] at hc
  · exact order_zero_on_real_axis rh hN z he
  · exact order_zero_low_positive hB z.property.2.2 hp ((le_abs_self _).trans hz)

lemma transform_even (y : ℝ) : EvenKernel.transform 4 (-y) = EvenKernel.transform 4 y := by
  unfold EvenKernel.transform
  apply intervalIntegral.integral_congr
  intro u _
  simp

noncomputable def absolutePacket (δ : ℝ) (z : PsiSmoothing.Zero) :=
  |packet δ z.val.im| * (IEANTN.zetaOrder z.val : ℝ)

lemma absolutePacket_conjugate (δ : ℝ) (z : PsiSmoothing.Zero) :
    absolutePacket δ (conjugate z) = absolutePacket δ z := by
  change |packet δ (-z.val.im)| * (IEANTN.zetaOrder (starRingEnd ℂ z.val) : ℝ) = _
  rw [CH2Section6.zetaOrder_conj]
  simp only [packet, mul_neg, transform_even]
  rfl

lemma absolutePacket_low (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound) (δ : ℝ) (z : PsiSmoothing.Zero)
    (hz : |z.val.im| ≤ 12) : absolutePacket δ z = 0 := by
  simp [absolutePacket, order_zero_low rh hN hB z hz]

def positiveEquiv (rh : RiemannHypothesis) :
    {z : PsiSmoothing.Zero // 12 < z.val.im} ≃ RHOcticPush.BPTInfinite.PositiveZero 12 where
  toFun z := ⟨z.val.val, mem_univ _, z.property, z.val.property.2.2⟩
  invFun z := by
    have hr : z.val.re = 1 / 2 := by
      apply rh z.val z.property.2.2
      · rintro ⟨n, hn⟩
        have him := congrArg Complex.im hn
        norm_num at him
        have hi : (12 : ℝ) < z.val.im := z.property.2.1
        linarith
      · intro hn
        have him := congrArg Complex.im hn
        norm_num at him
        have hi : (12 : ℝ) < z.val.im := z.property.2.1
        linarith
    exact ⟨⟨z.val, ⟨by rw [hr]; norm_num, by rw [hr]; norm_num⟩,
      mem_univ _, z.property.2.2⟩, z.property.2.1⟩
  left_inv z := Subtype.ext (Subtype.ext rfl)
  right_inv z := Subtype.ext rfl

lemma absolutePacket_nonneg (δ : ℝ) (z : PsiSmoothing.Zero) :
    0 ≤ absolutePacket δ z :=
  mul_nonneg (abs_nonneg _) (by exact_mod_cast order_nonneg z)

lemma absolutePacket_summable (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) {δ : ℝ} (hδ : 0 < δ) :
    Summable (absolutePacket δ) := by
  apply Summable.of_nonneg_of_le (absolutePacket_nonneg δ) _
    ((weight_summable rh hN).mul_left (envelope δ))
  intro z
  have ho : (0 : ℝ) ≤ IEANTN.zetaOrder z := by exact_mod_cast order_nonneg z
  rw [absolutePacket, packet, abs_mul, abs_of_pos hδ, weight_eq rh]
  calc
      _ ≤ (envelope δ / (1 / 4 + z.val.im ^ 2)) * (IEANTN.zetaOrder z : ℝ) :=
        mul_le_mul_of_nonneg_right (scaled_transform_majorant hδ) ho
      _ = _ := by ring

noncomputable def positivePart (δ : ℝ) (z : PsiSmoothing.Zero) :=
  if 12 < z.val.im then absolutePacket δ z else 0
noncomputable def negativePart (δ : ℝ) (z : PsiSmoothing.Zero) :=
  if z.val.im < -12 then absolutePacket δ z else 0

lemma positivePart_summable (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) {δ : ℝ} (hδ : 0 < δ) :
    Summable (positivePart δ) := by
  apply Summable.of_nonneg_of_le (fun z => by
    dsimp [positivePart]; split_ifs <;> simp_all [absolutePacket_nonneg]) _
    (absolutePacket_summable rh hN hδ)
  intro z
  dsimp [positivePart]
  split_ifs <;> simp_all [absolutePacket_nonneg]

lemma negative_eq_positive_conjugate (δ : ℝ) (z : PsiSmoothing.Zero) :
    negativePart δ z = positivePart δ (conjugate z) := by
  unfold positivePart negativePart
  change (if z.val.im < -12 then _ else _) = (if 12 < -z.val.im then _ else _)
  rw [absolutePacket_conjugate]
  have hi : (z.val.im < -12) ↔ (12 < -z.val.im) := by
    constructor <;> intro h <;> linarith
  simp only [hi]

lemma negativePart_summable (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) {δ : ℝ} (hδ : 0 < δ) :
    Summable (negativePart δ) := by
  have hs := (conjugate.summable_iff).mpr (positivePart_summable rh hN hδ)
  exact hs.congr (fun z => (negative_eq_positive_conjugate δ z).symm)

lemma absolutePacket_split (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound) (δ : ℝ) (z : PsiSmoothing.Zero) :
    absolutePacket δ z = positivePart δ z + negativePart δ z := by
  by_cases hp : 12 < z.val.im
  · have hn : ¬ z.val.im < -12 := by linarith
    simp [positivePart, negativePart, hp, hn]
  · by_cases hn : z.val.im < -12
    · simp [positivePart, negativePart, hp, hn]
    · have hz : |z.val.im| ≤ 12 := by rw [abs_le]; constructor <;> linarith
      simp [positivePart, negativePart, hp, hn, absolutePacket_low rh hN hB δ z hz]

/-- Exact full-family pairing. In particular, the real-axis and all low-height
packets have been discharged, rather than omitted from a finite approximation. -/
theorem full_absolute_pairing (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound) {δ : ℝ} (hδ : 0 < δ) :
    (∑' z : PsiSmoothing.Zero, absolutePacket δ z) =
      2 * ∑' z : RHOcticPush.BPTInfinite.PositiveZero 12,
        |packet δ z.val.im| * (IEANTN.zetaOrder z.val : ℝ) := by
  have hp := positivePart_summable rh hN hδ
  have hn := negativePart_summable rh hN hδ
  have he : (∑' z : PsiSmoothing.Zero, negativePart δ z) =
      ∑' z : PsiSmoothing.Zero, positivePart δ z := by
    simp_rw [negative_eq_positive_conjugate]
    exact conjugate.tsum_eq _
  have ht : (∑' z : PsiSmoothing.Zero, positivePart δ z) =
      ∑' z : RHOcticPush.BPTInfinite.PositiveZero 12,
        |packet δ z.val.im| * (IEANTN.zetaOrder z.val : ℝ) := by
    rw [show positivePart δ = {z : PsiSmoothing.Zero | 12 < z.val.im}.indicator
      (absolutePacket δ) by rfl,
      ← tsum_subtype {z : PsiSmoothing.Zero | 12 < z.val.im} (absolutePacket δ)]
    exact (positiveEquiv rh).tsum_eq (fun z : RHOcticPush.BPTInfinite.PositiveZero 12 =>
      |packet δ z.val.im| * (IEANTN.zetaOrder z.val : ℝ))
  calc
    _ = ∑' z : PsiSmoothing.Zero, (positivePart δ z + negativePart δ z) :=
      tsum_congr (absolutePacket_split rh hN hB δ)
    _ = (∑' z : PsiSmoothing.Zero, positivePart δ z) +
        ∑' z : PsiSmoothing.Zero, negativePart δ z := hp.tsum_add hn
    _ = _ := by rw [he, ht]; ring

theorem zeroTerm_norm_le_positive_sum (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) :
    ‖EvenKernel.zeroTerm 4 C L‖ ≤
      2 * ∑' z : RHOcticPush.BPTInfinite.PositiveZero 12,
        |packet (EvenKernel.δ C L) z.val.im| * (IEANTN.zetaOrder z.val : ℝ) := by
  have he : (fun z : PsiSmoothing.Zero => ‖EvenKernel.zeroPacket 4 C L z‖) =
      absolutePacket (EvenKernel.δ C L) := by
    funext z
    rw [packet_norm hδ]
    simp only [absolutePacket, packet, abs_mul, abs_of_pos hδ]
  have h := norm_tsum_le_tsum_norm (packet_norm_summable rh hN hδ)
  change ‖EvenKernel.zeroTerm 4 C L‖ ≤ _ at h
  rw [he, full_absolute_pairing rh hN hB hδ] at h
  exact h

/-- Complete infinite-zero bound on the original consumer, before numerical
Fourier moment constants. All zero, height, multiplicity and tail bridges are consumed. -/
theorem zeroTerm_norm_le_BPT_integrals (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) :
    ‖EvenKernel.zeroTerm 4 C L‖ ≤
      2 * ((∫ t in Ioi 12, |packet (EvenKernel.δ C L) t| * RHLimit.BPTZeroCount.density t) +
        (7 / 25) * (|packet (EvenKernel.δ C L) 12| * Real.log 12 +
          ∫ t in Ioi 12, |packetDeriv (EvenKernel.δ C L) t| * Real.log t)) := by
  have h := octic_infinite_bound hB hδ
    (a := 12) (by linarith [Real.pi_lt_four])
  exact (zeroTerm_norm_le_positive_sum rh hN hB hδ).trans
    (mul_le_mul_of_nonneg_left h.2 (by norm_num))

#print axioms order_zero_low
#print axioms full_absolute_pairing
#print axioms zeroTerm_norm_le_BPT_integrals
end RHOcticPush.ZeroPairing
