import SynergyAnalytic.ReciprocalCells
namespace SynergyAnalytic
open Real Set MeasureTheory Finset Filter Topology
set_option maxHeartbeats 0

/-- A finite coefficient-vector handles low heights; an existing analytic
majorant handles the remaining infinite tail. The proof takes a limit of
finite partial-summation identities, so no desired reciprocal or improper
integrability premise is introduced. -/
theorem finite_reciprocal_cells_tail_boundary {α : Type*} (S : Finset α) (gamma w : α→ℝ)
    {a caps : ℕ→ℝ} {n : ℕ} {T0 tailCap boundaryCap : ℝ} {g boundary : ℝ→ℝ}
    (ha : Monotone a) (h0 : 0<a 0)
    (hg : ∀z∈S,a 0<gamma z ∧gamma z≤T0)
    (hcaps : ∀i<n,∀u∈Icc (a i) (a (i+1)),
      (∑z∈S,if gamma z≤u then w z else 0)≤caps i+boundary u)
    (hgc : ContinuousOn g (Ici (a n)))
    (htail : ∀u, a n≤u → (∑z∈S,if gamma z≤u then w z else 0)≤g u+boundary u)
    (htailCap : ∀T,a n≤T → (∫u in a n..T,g u/u^2)≤tailCap)
    (hbc : ContinuousOn boundary (Ici (a 0)))
    (hbCap : ∀T,a 0≤T → (∫u in a 0..T,boundary u/u^2)≤boundaryCap) :
    (∑z∈S,w z/gamma z)≤
      (∑i∈range n,caps i*(1/a i-1/a (i+1)))+tailCap+boundaryCap := by
  let C := ∑i∈range n,caps i*(1/a i-1/a (i+1))
  have hsumLim : Tendsto (fun T:ℝ => (∑z∈S,w z)/T+C+tailCap+boundaryCap) atTop (𝓝 (C+tailCap+boundaryCap)) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _:ℝ => ∑z∈S,w z) atTop (𝓝 _)).mul
      tendsto_inv_atTop_zero).add_const C |>.add_const tailCap |>.add_const boundaryCap
    simpa only [mul_inv_rev,zero_mul,mul_zero,zero_add,div_eq_mul_inv] using h
  apply ge_of_tendsto hsumLim
  filter_upwards [eventually_ge_atTop (max T0 (a n))] with T hT
  have hT0 : T0≤T := (le_max_left _ _).trans hT
  have hBT : a n≤T := (le_max_right _ _).trans hT
  have hAT : a 0≤T := (ha (Nat.zero_le n)).trans hBT
  obtain ⟨he,hi⟩ := CH2QRH.finite_reciprocal_partial_sum S gamma w h0 hAT
    (fun z hz => ⟨(hg z hz).1,(hg z hz).2.trans hT0⟩)
  have hiB : IntervalIntegrable (fun u=>boundary u/u^2) volume (a 0) T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hAT]
    intro u hu
    have hu0 : u≠0 := (h0.trans_le hu.1).ne'
    exact (((hbc u hu.1).mono Icc_subset_Ici_self).div
      ((continuousAt_id.pow 2).continuousWithinAt) (pow_ne_zero 2 hu0))
  let F : ℝ→ℝ := fun u => (∑z∈S,if gamma z≤u then w z else 0)-boundary u
  have hiF : IntervalIntegrable (fun u=>F u/u^2) volume (a 0) T := by
    convert hi.sub hiB using 1
    funext u
    dsimp [F]
    ring
  have hiPrefix := hiF.mono_set (show uIcc (a 0) (a n)⊆uIcc (a 0) T by
    rw [uIcc_of_le (ha (Nat.zero_le n)),uIcc_of_le hAT]
    exact Icc_subset_Icc le_rfl hBT)
  have hiTail := hiF.mono_set (show uIcc (a n) T⊆uIcc (a 0) T by
    rw [uIcc_of_le hBT,uIcc_of_le hAT]
    exact Icc_subset_Icc (ha (Nat.zero_le n)) le_rfl)
  have hgi : IntervalIntegrable (fun u=>g u/u^2) volume (a n) T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hBT]
    intro u hu
    have hu0 : u≠0 := (h0.trans_le ((ha (Nat.zero_le n)).trans hu.1)).ne'
    exact (((hgc u hu.1).mono Icc_subset_Ici_self).div ((continuousAt_id.pow 2).continuousWithinAt)
      (pow_ne_zero 2 hu0))
  have hm := intervalIntegral.integral_mono_on hBT hiTail hgi
    (fun u hu=>div_le_div_of_nonneg_right
      (show F u≤g u by dsimp [F];linarith [htail u hu.1]) (sq_nonneg u))
  have hTailBound := hm.trans (htailCap T hBT)
  have hPrefixBound := reciprocal_integral_cells ha h0 hiPrefix (fun i hin u hu =>
    show F u≤caps i by dsimp [F];linarith [hcaps i hin u hu])
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hiPrefix hiTail
  have hjoin : (∫u in a 0..T,(∑z∈S,if gamma z≤u then w z else 0)/u^2) =
      (∫u in a 0..T,F u/u^2)+(∫u in a 0..T,boundary u/u^2) := by
    rw [←intervalIntegral.integral_add hiF hiB]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp [F]
    ring
  have hbBound := hbCap T hAT
  rw [he,hjoin,←hsplit]
  dsimp [C] at hsumLim ⊢
  linarith

#print axioms finite_reciprocal_cells_tail_boundary
end SynergyAnalytic
