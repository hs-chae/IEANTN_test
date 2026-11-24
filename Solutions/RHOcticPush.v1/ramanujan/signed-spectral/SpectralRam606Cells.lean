import SpectralRamCore
namespace RHOcticPush.SpectralRam
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram RHOcticPush.Correlated
open RHOcticPush.Spectral076 RHOcticPush.BoxPerron
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option leancert.trust "kernel"

lemma lower_0 : (43840242703/200000000000 : ℝ) ≤ -88 / 100 + lowerNoMax (28448019/1048576 : ℝ) (113793801/4194304 : ℝ) := by
  unfold lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma upper_0 : 68 / 100 + upperPowers ((28448019/1048576 : ℝ) - 1) ≤ (1793225381193/1000000000000 : ℝ) := by
  unfold upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma numeric_0 : ∀ z ∈ Set.Icc (28448019/1048576 : ℝ) (113793801/4194304 : ℝ),
    (1 / 1000 : ℝ) ≤ SpectralRam.numericMargin (5199/2500 : ℝ) (43840242703/200000000000 : ℝ) (1793225381193/1000000000000 : ℝ) z := by
  unfold SpectralRam.numericMargin F H Q T budget profile q
  simp_rw [fullBase_explicit]
  certify_bound 60 (trust := kernel)

theorem gap_0 (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (28448019/1048576 : ℝ) ≤ z) (hu : z ≤ (113793801/4194304 : ℝ))
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (5199/2500 : ℝ) ≤ 2 * pN 20 (113793801/4194304 : ℝ) := by
    norm_num [pN, Finset.sum_range_succ, Nat.factorial]
  have ha := lower_0.trans (by
    linarith [lowerNoMax_le (28448019/1048576 : ℝ) (113793801/4194304 : ℝ)] :
      -88 / 100 + lowerNoMax (28448019/1048576 : ℝ) (113793801/4194304 : ℝ) ≤ -88 / 100 + lowerPowers (28448019/1048576 : ℝ) (113793801/4194304 : ℝ))
  have h := SpectralRam.actual_margin rh hN hI hTab hL hU
    (by norm_num : 27 ≤ (28448019/1048576 : ℝ)) (by norm_num : (113793801/4194304 : ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (5199/2500 : ℝ)) hk ha upper_0
  have hn := numeric_0 z ⟨hl, hu⟩
  rw [SpectralRam.numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

#print axioms numeric_0
#print axioms gap_0

lemma lower_1 : (214061379/976562500 : ℝ) ≤ -88 / 100 + lowerNoMax (113793801/4194304 : ℝ) (56897763/2097152 : ℝ) := by
  unfold lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma upper_1 : 68 / 100 + upperPowers ((113793801/4194304 : ℝ) - 1) ≤ (1793221689933/1000000000000 : ℝ) := by
  unfold upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma numeric_1 : ∀ z ∈ Set.Icc (113793801/4194304 : ℝ) (56897763/2097152 : ℝ),
    (1 / 1000 : ℝ) ≤ SpectralRam.numericMargin (5199/2500 : ℝ) (214061379/976562500 : ℝ) (1793221689933/1000000000000 : ℝ) z := by
  unfold SpectralRam.numericMargin F H Q T budget profile q
  simp_rw [fullBase_explicit]
  certify_bound 60 (trust := kernel)

theorem gap_1 (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (113793801/4194304 : ℝ) ≤ z) (hu : z ≤ (56897763/2097152 : ℝ))
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (5199/2500 : ℝ) ≤ 2 * pN 20 (56897763/2097152 : ℝ) := by
    norm_num [pN, Finset.sum_range_succ, Nat.factorial]
  have ha := lower_1.trans (by
    linarith [lowerNoMax_le (113793801/4194304 : ℝ) (56897763/2097152 : ℝ)] :
      -88 / 100 + lowerNoMax (113793801/4194304 : ℝ) (56897763/2097152 : ℝ) ≤ -88 / 100 + lowerPowers (113793801/4194304 : ℝ) (56897763/2097152 : ℝ))
  have h := SpectralRam.actual_margin rh hN hI hTab hL hU
    (by norm_num : 27 ≤ (113793801/4194304 : ℝ)) (by norm_num : (56897763/2097152 : ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (5199/2500 : ℝ)) hk ha upper_1
  have hn := numeric_1 z ⟨hl, hu⟩
  rw [SpectralRam.numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

#print axioms numeric_1
#print axioms gap_1

lemma lower_2 : (219193815289/1000000000000 : ℝ) ≤ -88 / 100 + lowerNoMax (56897763/2097152 : ℝ) (1778109/65536 : ℝ) := by
  unfold lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma upper_2 : 68 / 100 + upperPowers ((56897763/2097152 : ℝ) - 1) ≤ (56038062467/31250000000 : ℝ) := by
  unfold upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma numeric_2 : ∀ z ∈ Set.Icc (56897763/2097152 : ℝ) (1778109/65536 : ℝ),
    (1 / 1000 : ℝ) ≤ SpectralRam.numericMargin (5199/2500 : ℝ) (219193815289/1000000000000 : ℝ) (56038062467/31250000000 : ℝ) z := by
  unfold SpectralRam.numericMargin F H Q T budget profile q
  simp_rw [fullBase_explicit]
  certify_bound 60 (trust := kernel)

theorem gap_2 (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (56897763/2097152 : ℝ) ≤ z) (hu : z ≤ (1778109/65536 : ℝ))
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (5199/2500 : ℝ) ≤ 2 * pN 20 (1778109/65536 : ℝ) := by
    norm_num [pN, Finset.sum_range_succ, Nat.factorial]
  have ha := lower_2.trans (by
    linarith [lowerNoMax_le (56897763/2097152 : ℝ) (1778109/65536 : ℝ)] :
      -88 / 100 + lowerNoMax (56897763/2097152 : ℝ) (1778109/65536 : ℝ) ≤ -88 / 100 + lowerPowers (56897763/2097152 : ℝ) (1778109/65536 : ℝ))
  have h := SpectralRam.actual_margin rh hN hI hTab hL hU
    (by norm_num : 27 ≤ (56897763/2097152 : ℝ)) (by norm_num : (1778109/65536 : ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (5199/2500 : ℝ)) hk ha upper_2
  have hn := numeric_2 z ⟨hl, hu⟩
  rw [SpectralRam.numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

#print axioms numeric_2
#print axioms gap_2

lemma lower_3 : (219183743287/1000000000000 : ℝ) ≤ -88 / 100 + lowerNoMax (1778109/65536 : ℝ) (28451469/1048576 : ℝ) := by
  unfold lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma upper_3 : 68 / 100 + upperPowers ((1778109/65536 : ℝ) - 1) ≤ (896605308887/500000000000 : ℝ) := by
  unfold upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma numeric_3 : ∀ z ∈ Set.Icc (1778109/65536 : ℝ) (28451469/1048576 : ℝ),
    (1 / 1000 : ℝ) ≤ SpectralRam.numericMargin (5199/2500 : ℝ) (219183743287/1000000000000 : ℝ) (896605308887/500000000000 : ℝ) z := by
  unfold SpectralRam.numericMargin F H Q T budget profile q
  simp_rw [fullBase_explicit]
  certify_bound 60 (trust := kernel)

theorem gap_3 (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1778109/65536 : ℝ) ≤ z) (hu : z ≤ (28451469/1048576 : ℝ))
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (5199/2500 : ℝ) ≤ 2 * pN 20 (28451469/1048576 : ℝ) := by
    norm_num [pN, Finset.sum_range_succ, Nat.factorial]
  have ha := lower_3.trans (by
    linarith [lowerNoMax_le (1778109/65536 : ℝ) (28451469/1048576 : ℝ)] :
      -88 / 100 + lowerNoMax (1778109/65536 : ℝ) (28451469/1048576 : ℝ) ≤ -88 / 100 + lowerPowers (1778109/65536 : ℝ) (28451469/1048576 : ℝ))
  have h := SpectralRam.actual_margin rh hN hI hTab hL hU
    (by norm_num : 27 ≤ (1778109/65536 : ℝ)) (by norm_num : (28451469/1048576 : ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (5199/2500 : ℝ)) hk ha upper_3
  have hn := numeric_3 z ⟨hl, hu⟩
  rw [SpectralRam.numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

#print axioms numeric_3
#print axioms gap_3

lemma lower_4 : (219163605727/1000000000000 : ℝ) ≤ -88 / 100 + lowerNoMax (28451469/1048576 : ℝ) (28454919/1048576 : ℝ) := by
  unfold lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma upper_4 : 68 / 100 + upperPowers ((28451469/1048576 : ℝ) - 1) ≤ (1793195858667/1000000000000 : ℝ) := by
  unfold upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma numeric_4 : ∀ z ∈ Set.Icc (28451469/1048576 : ℝ) (28454919/1048576 : ℝ),
    (1 / 1000 : ℝ) ≤ SpectralRam.numericMargin (5199/2500 : ℝ) (219163605727/1000000000000 : ℝ) (1793195858667/1000000000000 : ℝ) z := by
  unfold SpectralRam.numericMargin F H Q T budget profile q
  simp_rw [fullBase_explicit]
  certify_bound 60 (trust := kernel)

theorem gap_4 (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (28451469/1048576 : ℝ) ≤ z) (hu : z ≤ (28454919/1048576 : ℝ))
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (5199/2500 : ℝ) ≤ 2 * pN 20 (28454919/1048576 : ℝ) := by
    norm_num [pN, Finset.sum_range_succ, Nat.factorial]
  have ha := lower_4.trans (by
    linarith [lowerNoMax_le (28451469/1048576 : ℝ) (28454919/1048576 : ℝ)] :
      -88 / 100 + lowerNoMax (28451469/1048576 : ℝ) (28454919/1048576 : ℝ) ≤ -88 / 100 + lowerPowers (28451469/1048576 : ℝ) (28454919/1048576 : ℝ))
  have h := SpectralRam.actual_margin rh hN hI hTab hL hU
    (by norm_num : 27 ≤ (28451469/1048576 : ℝ)) (by norm_num : (28454919/1048576 : ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (5199/2500 : ℝ)) hk ha upper_4
  have hn := numeric_4 z ⟨hl, hu⟩
  rw [SpectralRam.numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

#print axioms numeric_4
#print axioms gap_4

theorem bridge606 (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (606000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 610000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp (28448019/1048576 : ℝ) ≤ (606000000000 : ℝ) := by
    interval_decide 80 (trust := kernel)
  have hup : (610000000000 : ℝ) ≤ exp (28454919/1048576 : ℝ) := by
    interval_decide 80 (trust := kernel)
  have hl : (28448019/1048576 : ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ (28454919/1048576 : ℝ) := exp_le_exp.mp (hcap.trans hup)
  have hc : (480000000000 : ℝ) ≤ exp z := by linarith
  have hp : exp z ≤ (640000000000 : ℝ) := by linarith
  by_cases h0 : z ≤ (113793801/4194304 : ℝ)
  · exact gap_0 rh hN hI hTab hL hU (by linarith) h0 hc hp
  by_cases h1 : z ≤ (56897763/2097152 : ℝ)
  · exact gap_1 rh hN hI hTab hL hU (by linarith) h1 hc hp
  by_cases h2 : z ≤ (1778109/65536 : ℝ)
  · exact gap_2 rh hN hI hTab hL hU (by linarith) h2 hc hp
  by_cases h3 : z ≤ (28451469/1048576 : ℝ)
  · exact gap_3 rh hN hI hTab hL hU (by linarith) h3 hc hp
  exact gap_4 rh hN hI hTab hL hU (by linarith) hu hc hp

#print axioms bridge606
end RHOcticPush.SpectralRam
