import BoxEndpointBPT

namespace RHOcticPush.BoxZero
open Real Set MeasureTheory Filter
open RHLimit.BPTZeroCount RHOcticPush.BPTInfinite
set_option maxHeartbeats 0

theorem infinite_absolute_exact_endpoint_bound (h : PublishedBound) {a : ℝ}
    (ha : 2 * Real.pi ≤ a) {f f' : ℝ → ℝ}
    (hd : ∀ t ∈ Ici a, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Ici a))
    (hI : IntegrableOn (fun t => |f t| * density t) (Ioi a))
    (hD : IntegrableOn (fun t => |f' t| * log t) (Ioi a))
    (hb : Tendsto (fun t => |f t| * log t) atTop (nhds 0)) :
    Summable (fun z : PositiveZero a => |f z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ∧
    (∑' z : PositiveZero a, |f z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ≤
      (∫ t in Ioi a, |f t| * density t) +
      (7 / 25) * (∫ t in Ioi a, |f' t| * log t) + |f a| * |remainder a| := by
  classical
  let B := (∫ t in Ioi a, |f t| * density t) +
    (7 / 25) * (∫ t in Ioi a, |f' t| * log t) + |f a| * |remainder a|
  have ha0 : 0 ≤ a := by linarith [pi_pos]
  have hnonneg (z : PositiveZero a) :
      0 ≤ |f z.val.im| * (IEANTN.zetaOrder z.val : ℝ) :=
    mul_nonneg (abs_nonneg _) (order_nonneg ha0 z)
  have hsum (s : Finset (PositiveZero a)) :
      (∑ z ∈ s, |f z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ≤ B := by
    let M := ∑ z ∈ s, max z.val.im 0
    have hM (z : PositiveZero a) (hz : z ∈ s) : z.val.im ≤ M := by
      exact (le_max_left _ _).trans (Finset.single_le_sum
        (fun v _ => le_max_right v.val.im 0) hz)
    have hmain := intervalIntegral_tendsto_integral_Ioi a hI tendsto_id
    have hder := intervalIntegral_tendsto_integral_Ioi a hD tendsto_id
    have hrest := ((hb.add hder).const_mul (7 / 25 : ℝ)).add_const (|f a| * |remainder a|)
    have hlim := hmain.add hrest
    have hlim' : Tendsto
        (fun b : ℝ => (∫ t in a..b, |f t| * density t) +
          (7 / 25) * (|f b| * log b +
            ∫ t in a..b, |f' t| * log t) + |f a| * |remainder a|) atTop (nhds B) := by
      simpa [B,add_assoc] using hlim
    apply ge_of_tendsto hlim'
    filter_upwards [eventually_ge_atTop (max a M)] with b hlarge
    have hab : a ≤ b := (le_max_left _ _).trans hlarge
    have hs : ∀ z ∈ s, z.val.im ≤ b := fun z hz =>
      (hM z hz).trans ((le_max_right _ _).trans hlarge)
    apply (finite_subsum_le ha0 f s hs).trans
    apply finite_absolute_exact_endpoint_bound h ha hab
    · intro t ht
      rw [uIcc_of_le hab] at ht
      exact hd t ht.1
    · exact hc.mono (by intro t ht; rw [uIcc_of_le hab] at ht; exact ht.1)
  exact ⟨summable_of_sum_le hnonneg hsum, Real.tsum_le_of_sum_le hnonneg hsum⟩


/-- At the actual cutoff12 the exact lower remainder is minus the RvM main term.
The zero count is proved from BPT; no zero-table computation is assumed. -/
theorem infinite_absolute_twelve (h : PublishedBound) {f f' : ℝ → ℝ}
    (hd : ∀ t ∈ Ici 12, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Ici 12))
    (hI : IntegrableOn (fun t => |f t| * density t) (Ioi 12))
    (hD : IntegrableOn (fun t => |f' t| * log t) (Ioi 12))
    (hb : Tendsto (fun t => |f t| * log t) atTop (nhds 0)) :
    Summable (fun z : PositiveZero 12 => |f z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ∧
    (∑' z : PositiveZero 12, |f z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ≤
      (∫ t in Ioi 12, |f t| * density t) +
      (7 / 25) * (∫ t in Ioi 12, |f' t| * log t) +
        |f 12| * |ZeroCount.v1.rvmMain 12| := by
  have he : remainder 12 = -ZeroCount.v1.rvmMain 12 := by
    simp only [remainder, count_twelve_zero h, zero_sub]
  simpa only [he, abs_neg] using infinite_absolute_exact_endpoint_bound h
    (by linarith [Real.pi_lt_four] : 2 * Real.pi ≤ (12 : ℝ)) hd hc hI hD hb

#print axioms infinite_absolute_exact_endpoint_bound
#print axioms infinite_absolute_twelve
end RHOcticPush.BoxZero
