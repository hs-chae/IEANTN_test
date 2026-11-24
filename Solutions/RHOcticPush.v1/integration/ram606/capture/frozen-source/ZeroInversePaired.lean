import ZeroInverseBand

/-! Both signs of the actual finite zero family. This independently checks a
normalization in a published finite reciprocal-zero sum, without a zero table. -/
namespace RHOcticPush.ZeroComparison
open Real Complex Set MeasureTheory
open RHLimit.BPTZeroCount
set_option maxHeartbeats 0

noncomputable def positiveFinset : Finset ℂ :=
  (CH2Section7Z.finite_zeros_Ioc (a := 0) (b := 10000000) le_rfl).toFinset
noncomputable def pairedFinset : Finset ℂ :=
  positiveFinset ∪ positiveFinset.image (starRingEnd ℂ)
noncomputable def inverseWeight (z : ℂ) : ℝ :=
  (1/|z.im|)*(IEANTN.zetaOrder z : ℝ)

lemma mem_positiveFinset (z : ℂ) :
    z ∈ positiveFinset ↔ (0 < z.im ∧ z.im ≤ 10000000) ∧ riemannZeta z = 0 := by
  simp [positiveFinset, IEANTN.zetaZeroesIn, IEANTN.zetaZeroes]

lemma paired_disjoint : Disjoint positiveFinset (positiveFinset.image (starRingEnd ℂ)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hi
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
  have hh := ((mem_positiveFinset _).mp hz).1.1
  have hw0 := ((mem_positiveFinset _).mp hw).1.1
  simp only [Complex.conj_im] at hh
  linarith

lemma inverseWeight_conjugate (z : ℂ) :
    inverseWeight (starRingEnd ℂ z) = inverseWeight z := by
  simp [inverseWeight, Complex.conj_im, CH2Section6.zetaOrder_conj]

lemma paired_sum : (∑ z ∈ pairedFinset, inverseWeight z) =
    2 * ∑ z ∈ positiveFinset, (1/z.im)*(IEANTN.zetaOrder z : ℝ) := by
  classical
  unfold pairedFinset
  rw [Finset.sum_union paired_disjoint, Finset.sum_image]
  · simp_rw [inverseWeight_conjugate]
    have he : (∑ z ∈ positiveFinset, inverseWeight z) =
        ∑ z ∈ positiveFinset, (1/z.im)*(IEANTN.zetaOrder z : ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      unfold inverseWeight
      rw [abs_of_pos (((mem_positiveFinset z).mp hz).1.1)]
    rw [he]
    ring
  · intro z _ w _ hh
    simpa only [Complex.conj_conj] using congrArg (starRingEnd ℂ) hh

lemma positive_sum_lower (h : PublishedBound) :
    (14 : ℝ) < ∑ z ∈ positiveFinset, (1/z.im)*(IEANTN.zetaOrder z : ℝ) := by
  classical
  have hh := positive_inverse_band h
  let B := (CH2Section7Z.finite_zeros_Ioc (a := 1000) (b := 10000000)
    (by norm_num)).toFinset
  rw [CH2Section7Z.zetaZeroesSum_eq_sum
    (CH2Section7Z.finite_zeros_Ioc (a := 1000) (b := 10000000) (by norm_num))] at hh
  apply hh.trans_le
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    have hm := (Set.Finite.mem_toFinset _).mp hz
    apply (mem_positiveFinset z).mpr
    exact ⟨⟨by linarith [hm.2.1.1], hm.2.1.2⟩, hm.2.2⟩
  · intro z hz _
    have hp := (mem_positiveFinset z).mp hz
    have ho : (0 : ℝ) ≤ IEANTN.zetaOrder z :=
      CH2Section7Z.zetaOrder_nonneg_of_mem Ioc_subset_Ioi_self
        (show z ∈ IEANTN.zetaZeroesIn Set.univ (Ioc 0 10000000) from
          ⟨mem_univ _, hp.1, hp.2⟩)
    exact mul_nonneg (div_nonneg zero_le_one hp.1.1.le) ho

lemma paired_set_identity :
    (pairedFinset : Set ℂ) =
      IEANTN.zetaZeroesIn Set.univ {t : ℝ | 0 < |t| ∧ |t| ≤ 10000000} := by
  classical
  ext z
  constructor
  · intro hz
    change z ∈ positiveFinset ∪ positiveFinset.image (starRingEnd ℂ) at hz
    rcases Finset.mem_union.mp hz with hp | hn
    · have hh := (mem_positiveFinset z).mp hp
      exact ⟨mem_univ _, by simpa only [Set.mem_setOf_eq, abs_of_pos hh.1.1] using hh.1, hh.2⟩
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
      have hh := (mem_positiveFinset w).mp hw
      refine ⟨mem_univ _, ?_, ?_⟩
      · simpa only [Set.mem_setOf_eq, Complex.conj_im, abs_neg, abs_of_pos hh.1.1] using hh.1
      · change riemannZeta (starRingEnd ℂ w) = 0
        rw [riemannZeta_conj, hh.2, map_zero]
  · rintro ⟨_, hh, hz⟩
    change z ∈ positiveFinset ∪ positiveFinset.image (starRingEnd ℂ)
    apply Finset.mem_union.mpr
    by_cases hp : 0 < z.im
    · left
      apply (mem_positiveFinset z).mpr
      exact ⟨⟨hp, by simpa only [abs_of_pos hp] using hh.2⟩, hz⟩
    · right
      have hn : z.im < 0 := by
        have h0 := hh.1
        rw [abs_pos] at h0
        exact lt_of_le_of_ne (le_of_not_gt hp) h0
      refine Finset.mem_image.mpr ⟨starRingEnd ℂ z, ?_, by simp⟩
      apply (mem_positiveFinset _).mpr
      refine ⟨⟨by simpa using neg_pos.mpr hn, ?_⟩, ?_⟩
      · simpa only [Complex.conj_im, abs_of_neg hn] using hh.2
      · rw [riemannZeta_conj, hz, map_zero]

/-- The exact complete finite both-sign sum, including every multiplicity. -/
theorem actual_both_sign_inverse_lower (h : PublishedBound) :
    (28 : ℝ) < IEANTN.zetaZeroesSum Set.univ
      {t : ℝ | 0 < |t| ∧ |t| ≤ 10000000} (fun z => 1/|z.im|) := by
  have hf : (IEANTN.zetaZeroesIn Set.univ
      {t : ℝ | 0 < |t| ∧ |t| ≤ 10000000}).Finite := by
    rw [← paired_set_identity]
    exact pairedFinset.finite_toSet
  have he : hf.toFinset = pairedFinset := by
    classical
    ext z
    rw [Set.Finite.mem_toFinset, ← paired_set_identity]
    rfl
  rw [CH2Section7Z.zetaZeroesSum_eq_sum hf, he]
  change (28 : ℝ) < ∑ z ∈ pairedFinset, inverseWeight z
  rw [paired_sum]
  linarith [positive_sum_lower h]

theorem excludes_both_sign_sixteen (h : PublishedBound) :
    ¬IEANTN.zetaZeroesSum Set.univ
      {t : ℝ | 0 < |t| ∧ |t| ≤ 10000000} (fun z => 1/|z.im|) ≤
        (162106480369/10000000000 : ℝ) := by
  have hh := actual_both_sign_inverse_lower h
  linarith

#print axioms actual_both_sign_inverse_lower
#print axioms excludes_both_sign_sixteen
end RHOcticPush.ZeroComparison
