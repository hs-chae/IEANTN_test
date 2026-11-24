import BoxQuadraticTail
import BoxZeroScalar

/-! Honest finite low-height population and full high-height reciprocal-square
sum on the actual positive-zero subtype, including every multiplicity. -/
namespace RHOcticPush.BoxZero
open Real Set MeasureTheory Filter
open RHLimit.BPTZeroCount RHOcticPush.BPTInfinite
set_option maxHeartbeats 0

lemma positive_finite_count_le {T : ℝ} (s : Finset (PositiveZero 12))
    (hs : ∀ z ∈ s,z.val.im≤T) :
    (∑ z ∈ s,(IEANTN.zetaOrder z.val : ℝ)) ≤ ZeroCount.v1.zetaNClosed T := by
  classical
  let Z := (CH2Section7Z.finite_zeros_Ioc (a := 0) (b := T) le_rfl).toFinset
  have hsub : s.image Subtype.val ⊆ Z := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    exact (Set.Finite.mem_toFinset _).mpr
      ⟨mem_univ _,⟨by have hh : (12:ℝ)<v.val.im := v.property.2.1;linarith,hs v hv⟩,v.property.2.2⟩
  unfold ZeroCount.v1.zetaNClosed
  rw [CH2Section7Z.zetaZeroesSum_eq_sum
    (CH2Section7Z.finite_zeros_Ioc (a := 0) (b := T) le_rfl)]
  simp only [one_mul]
  calc
    _ = ∑ z ∈ s.image Subtype.val,(IEANTN.zetaOrder z : ℝ) := by
      rw [Finset.sum_image]
      intro z _ v _ hv
      exact Subtype.ext hv
    _ ≤ ∑ z ∈ Z,(IEANTN.zetaOrder z : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro z hz _
      exact CH2Section7Z.zetaOrder_nonneg_of_mem Ioc_subset_Ioi_self
        ((Set.Finite.mem_toFinset _).mp hz)

noncomputable def countPiece (T : ℝ) (z : PositiveZero 12) : ℝ :=
  if z.val.im≤T then (IEANTN.zetaOrder z.val : ℝ) else 0

lemma countPiece_nonneg (T : ℝ) (z : PositiveZero 12) : 0≤countPiece T z := by
  unfold countPiece
  split_ifs
  · exact order_nonneg (by norm_num) z
  · rfl

/-- Summability is proved from genuine finite subsets, not from totalized tsum. -/
theorem countPiece_bound (T : ℝ) : Summable (countPiece T) ∧
    (∑' z : PositiveZero 12,countPiece T z) ≤ ZeroCount.v1.zetaNClosed T := by
  classical
  have hs (s : Finset (PositiveZero 12)) :
      (∑ z ∈ s,countPiece T z) ≤ ZeroCount.v1.zetaNClosed T := by
    unfold countPiece
    rw [← Finset.sum_filter]
    exact positive_finite_count_le _ (fun z hz => (Finset.mem_filter.mp hz).2)
  exact ⟨summable_of_sum_le (countPiece_nonneg T) hs,
    Real.tsum_le_of_sum_le (countPiece_nonneg T) hs⟩

def tailEquiv {T : ℝ} (hT : 12≤T) :
    {z : PositiveZero 12 // T<z.val.im} ≃ PositiveZero T where
  toFun z := ⟨z.val.val,mem_univ _,z.property,z.val.property.2.2⟩
  invFun z := ⟨⟨z.val,mem_univ _,hT.trans_lt z.property.2.1,z.property.2.2⟩,z.property.2.1⟩
  left_inv z := Subtype.ext (Subtype.ext rfl)
  right_inv z := Subtype.ext rfl

noncomputable def tailPiece (T : ℝ) (z : PositiveZero 12) : ℝ :=
  if T<z.val.im then (1/z.val.im^2)*(IEANTN.zetaOrder z.val : ℝ) else 0

lemma tailPiece_nonneg (T : ℝ) (z : PositiveZero 12) : 0≤tailPiece T z := by
  unfold tailPiece
  split_ifs
  · exact mul_nonneg (by positivity) (order_nonneg (by norm_num) z)
  · rfl

theorem tailPiece_bound (h : PublishedBound) {T : ℝ} (hT : 12≤T) :
    Summable (tailPiece T) ∧
    (∑' z : PositiveZero 12,tailPiece T z) ≤
      (log (T/(2*Real.pi))+1)/(2*Real.pi*T) + (7/25)*(3*log T+2)/T^2 := by
  have hd : 2*Real.pi≤T := by linarith [Real.pi_lt_four]
  have hq := quadratic_tail_bound h hd
  have hsub : Summable (fun z : {z : PositiveZero 12 // T<z.val.im} =>
      (1/z.val.val.im^2)*(IEANTN.zetaOrder z.val.val : ℝ)) :=
    (tailEquiv hT).summable_iff.mpr hq.1
  have hs : Summable (tailPiece T) := by
    change Summable ({z : PositiveZero 12 | T<z.val.im}.indicator
      (fun z => (1/z.val.im^2)*(IEANTN.zetaOrder z.val : ℝ)))
    exact summable_subtype_iff_indicator.mp hsub
  have he : (∑' z : PositiveZero 12,tailPiece T z) =
      ∑' z : PositiveZero T,(1/z.val.im^2)*(IEANTN.zetaOrder z.val : ℝ) := by
    change (∑' z : PositiveZero 12,{z : PositiveZero 12 | T<z.val.im}.indicator
      (fun z => (1/z.val.im^2)*(IEANTN.zetaOrder z.val : ℝ)) z) = _
    rw [← tsum_subtype {z : PositiveZero 12 | T<z.val.im}
      (fun z : PositiveZero 12 => (1/z.val.im^2)*(IEANTN.zetaOrder z.val : ℝ))]
    exact (tailEquiv hT).tsum_eq (fun z : PositiveZero T =>
      (1/z.val.im^2)*(IEANTN.zetaOrder z.val : ℝ))
  exact ⟨hs,he.trans_le hq.2⟩

/-- The fixed finite count and infinite tail are genuine BPT consequences. -/
theorem fixed_transport_bounds (h : PublishedBound) :
    (∑' z : PositiveZero 12,countPiece 32768 z) ≤ 40000 ∧
    (∑' z : PositiveZero 12,tailPiece 32768 z) ≤ 1/20000 := by
  have hn := h 32768 (by linarith [Real.pi_lt_four] : 2*Real.pi≤32768)
  have hc : ZeroCount.v1.zetaNClosed 32768 < 40000 := by
    have he : ZeroCount.v1.rvmMain 32768 = mainCount 32768 := rfl
    have hb := (le_abs_self _).trans hn
    rw [he] at hb
    linarith [count_height_upper]
  exact ⟨(countPiece_bound 32768).2.trans hc.le,
    (tailPiece_bound h (by norm_num : (12:ℝ)≤32768)).2.trans quadratic_tail_scalar.le⟩

#print axioms countPiece_bound
#print axioms tailPiece_bound
#print axioms fixed_transport_bounds
end RHOcticPush.BoxZero
