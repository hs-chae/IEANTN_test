import BPTZeroCount

/-! Endpoint-convention adapter for BPT Corollary1. The input is used only at
heights which are not zero ordinates, where open, closed and half-weight counts
coincide. Local finiteness and a right limit prove the actual closed-count bound
at every height, including2π and zero ordinates, with unchanged constants. -/
namespace RHOcticPush.BPTSourceEndpoint
open Real Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 0

/-- Conservative common part of the published source, independent of any
convention at jump points. This remains an explicit literature hypothesis. -/
def SourceBPTOffOrdinate : Prop :=
  ∀ T : ℝ, 2 * Real.pi < T →
    (∀ z : ℂ, riemannZeta z = 0 → 0 < z.im → z.im ≠ T) →
      |ZeroCount.v1.zetaNClosed T - ZeroCount.v1.rvmMain T| ≤ (7 / 25) * Real.log T

lemma right_gap_and_count {T : ℝ} (hT : 0 ≤ T) :
    ∀ᶠ t : ℝ in 𝓝[>] T,
      ZeroCount.v1.zetaNClosed t = ZeroCount.v1.zetaNClosed T ∧
      (∀ z : ℂ, riemannZeta z = 0 → 0 < z.im → z.im ≠ t) := by
  classical
  let Z := (CH2Section7Z.finite_zeros_Ioc (a := 0) (b := T + 1) le_rfl).toFinset
  have hgap : ∀ᶠ t : ℝ in 𝓝 T, ∀ z ∈ Z, T < z.im → t < z.im := by
    apply (Finset.eventually_all Z).mpr
    intro z _
    by_cases hz : T < z.im
    · filter_upwards [eventually_lt_nhds hz] with t ht
      exact fun _ => ht
    · exact Filter.Eventually.of_forall (fun _ h => (hz h).elim)
  filter_upwards [hgap.filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (show T < T + 1 by linarith)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t hg ht hgt
  have htt : T < t := hgt
  have ht0 : 0 ≤ t := hT.trans htt.le
  constructor
  · rw [CH2Section7Z.zetaNClosed_eq_sum ht0 ht.le,
      CH2Section7Z.zetaNClosed_eq_sum hT (by linarith : T ≤ T + 1)]
    apply Finset.sum_congr rfl
    intro z hz
    change (if z.im ≤ t then _ else _) = (if z.im ≤ T then _ else _)
    by_cases hzt : z.im ≤ T
    · simp only [if_pos hzt, if_pos (hzt.trans htt.le)]
    · have hgtz : t < z.im := hg z hz (lt_of_not_ge hzt)
      simp only [if_neg hzt, if_neg (not_le.mpr hgtz)]
  · intro z hz hzi he
    have hzmem : z ∈ Z := (Set.Finite.mem_toFinset _).mpr
      ⟨mem_univ _, ⟨hzi, by rw [he]; exact ht.le⟩, hz⟩
    have hzgt : T < z.im := by rw [he]; exact htt
    have hgtz := hg z hzmem hzgt
    rw [he] at hgtz
    exact (lt_irrefl t) hgtz

/-- A genuine proof of the unchanged source-to-closed-count contract.
Neither half a multiplicity nor an endpoint-error term is added. -/
theorem publishedBound_of_offOrdinate (hB : SourceBPTOffOrdinate) :
    RHLimit.BPTZeroCount.PublishedBound := by
  intro T hT
  have hT0 : 0 < T := by linarith [Real.pi_pos]
  have hm := (RHLimit.BPTZeroCount.main_hasDerivAt hT0).continuousAt.tendsto
  have hl := (Real.continuousAt_log hT0.ne').tendsto
  have hleft : Tendsto (fun t : ℝ => |ZeroCount.v1.zetaNClosed T - ZeroCount.v1.rvmMain t|)
      (𝓝[>] T) (nhds |ZeroCount.v1.zetaNClosed T - ZeroCount.v1.rvmMain T|) :=
    (tendsto_const_nhds.sub hm).abs.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun t : ℝ => (7 / 25) * log t)
      (𝓝[>] T) (nhds ((7 / 25) * log T)) :=
    (hl.const_mul (7 / 25 : ℝ)).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [right_gap_and_count hT0.le, self_mem_nhdsWithin] with t ht hgt
  have he := hB t (hT.trans_lt hgt) ht.2
  rwa [ht.1] at he

#print axioms right_gap_and_count
#print axioms publishedBound_of_offOrdinate
end RHOcticPush.BPTSourceEndpoint
