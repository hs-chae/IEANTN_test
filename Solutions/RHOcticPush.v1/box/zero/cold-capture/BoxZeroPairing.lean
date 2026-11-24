import OcticZeroPairing

/-! Generic complete even-majorant pairing on the actual zeta-zero family.
Summability of the entire family is deduced from the genuine positive-family
sum; the real axis and low heights are discharged by proved order-zero facts. -/
namespace RHOcticPush.BoxZero
open Real Complex Set Filter
open RHOcticPush.BPTInfinite
set_option maxHeartbeats 0

noncomputable def wholeWeight (g : ℝ → ℝ) (z : PsiSmoothing.Zero) : ℝ :=
  g z.val.im * (IEANTN.zetaOrder z.val : ℝ)
noncomputable def positiveWeight (g : ℝ → ℝ) : PsiSmoothing.Zero → ℝ :=
  {z : PsiSmoothing.Zero | 12<z.val.im}.indicator (wholeWeight g)
noncomputable def negativeWeight (g : ℝ → ℝ) : PsiSmoothing.Zero → ℝ :=
  {z : PsiSmoothing.Zero | z.val.im < -12}.indicator (wholeWeight g)

lemma wholeWeight_conjugate {g : ℝ → ℝ} (he : ∀ t,g (-t)=g t)
    (z : PsiSmoothing.Zero) :
    wholeWeight g (RHOcticPush.ZeroPairing.conjugate z) = wholeWeight g z := by
  unfold wholeWeight
  change g (-z.val.im) * (IEANTN.zetaOrder (starRingEnd ℂ z.val) : ℝ) = _
  rw [he,CH2Section6.zetaOrder_conj]

lemma wholeWeight_split (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound) (g : ℝ → ℝ) (z : PsiSmoothing.Zero) :
    wholeWeight g z = positiveWeight g z + negativeWeight g z := by
  by_cases hp : 12<z.val.im
  · have hn : ¬z.val.im < -12 := by linarith
    simp [positiveWeight,negativeWeight,Set.indicator,hp,hn]
  · by_cases hn : z.val.im < -12
    · simp [positiveWeight,negativeWeight,Set.indicator,hp,hn]
    · have hz : |z.val.im|≤12 := by rw [abs_le];constructor <;> linarith
      have ho := RHOcticPush.ZeroPairing.order_zero_low rh hN hB z hz
      simp [positiveWeight,negativeWeight,Set.indicator,hp,hn,wholeWeight,ho]

/-- Complete-family summability and exact positive/negative pairing. -/
theorem even_majorant_pairing (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound) {g : ℝ → ℝ}
    (he : ∀ t,g (-t)=g t)
    (hs : Summable (fun z : PositiveZero 12 => g z.val.im*(IEANTN.zetaOrder z.val : ℝ))) :
    Summable (wholeWeight g) ∧
      (∑' z : PsiSmoothing.Zero,wholeWeight g z) =
        2*(∑' z : PositiveZero 12,g z.val.im*(IEANTN.zetaOrder z.val : ℝ)) := by
  have hsub : Summable (fun z : {z : PsiSmoothing.Zero // 12<z.val.im} =>
      wholeWeight g z.val) :=
    (RHOcticPush.ZeroPairing.positiveEquiv rh).summable_iff.mpr hs
  have hp : Summable (positiveWeight g) := summable_subtype_iff_indicator.mp hsub
  have heconj (z : PsiSmoothing.Zero) :
      negativeWeight g z = positiveWeight g (RHOcticPush.ZeroPairing.conjugate z) := by
    unfold positiveWeight negativeWeight Set.indicator
    change (if z.val.im < -12 then wholeWeight g z else 0) =
      (if 12 < -z.val.im then wholeWeight g (RHOcticPush.ZeroPairing.conjugate z) else 0)
    rw [wholeWeight_conjugate he]
    have hi : (z.val.im < -12) ↔ (12 < -z.val.im) := by
      constructor <;> intro h <;> linarith
    simp only [hi]
  have hn : Summable (negativeWeight g) :=
    ((RHOcticPush.ZeroPairing.conjugate.summable_iff).mpr hp).congr
      (fun z => (heconj z).symm)
  have hw : Summable (wholeWeight g) :=
    (hp.add hn).congr (fun z => (wholeWeight_split rh hN hB g z).symm)
  have ht : (∑' z : PsiSmoothing.Zero,positiveWeight g z) =
      ∑' z : PositiveZero 12,g z.val.im*(IEANTN.zetaOrder z.val : ℝ) := by
    unfold positiveWeight
    rw [← tsum_subtype {z : PsiSmoothing.Zero | 12<z.val.im} (wholeWeight g)]
    exact (RHOcticPush.ZeroPairing.positiveEquiv rh).tsum_eq
      (fun z : PositiveZero 12 => g z.val.im*(IEANTN.zetaOrder z.val : ℝ))
  have hneg : (∑' z : PsiSmoothing.Zero,negativeWeight g z) =
      ∑' z : PsiSmoothing.Zero,positiveWeight g z := by
    simp_rw [heconj]
    exact RHOcticPush.ZeroPairing.conjugate.tsum_eq _
  refine ⟨hw,?_⟩
  calc
    _ = ∑' z : PsiSmoothing.Zero,(positiveWeight g z+negativeWeight g z) :=
      tsum_congr (wholeWeight_split rh hN hB g)
    _ = _ := by rw [hp.tsum_add hn,hneg,ht];ring

/-- A pointwise verified complex-packet majorant is consumed on the entire
actual zero family. The convergence of the packets themselves follows here. -/
theorem full_packet_bound (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound) {g : ℝ → ℝ} {p : PsiSmoothing.Zero → ℂ}
    (he : ∀ t,g (-t)=g t)
    (hs : Summable (fun z : PositiveZero 12 => g z.val.im*(IEANTN.zetaOrder z.val : ℝ)))
    (hp : ∀ z,‖p z‖≤wholeWeight g z) :
    Summable p ∧ ‖∑' z : PsiSmoothing.Zero,p z‖ ≤
      2*(∑' z : PositiveZero 12,g z.val.im*(IEANTN.zetaOrder z.val : ℝ)) := by
  have hw := even_majorant_pairing rh hN hB he hs
  have hnorm : Summable (fun z => ‖p z‖) :=
    Summable.of_nonneg_of_le (fun z => norm_nonneg _) hp hw.1
  have hsum : Summable p := hnorm.of_norm
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑' z : PsiSmoothing.Zero,‖p z‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' z : PsiSmoothing.Zero,wholeWeight g z := hnorm.tsum_le_tsum hp hw.1
    _ = _ := hw.2

#print axioms even_majorant_pairing
#print axioms full_packet_bound
end RHOcticPush.BoxZero
