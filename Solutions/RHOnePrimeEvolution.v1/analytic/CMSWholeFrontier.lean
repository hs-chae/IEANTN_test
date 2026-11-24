/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import CMSOpenTransfer

/-! The complete source-conditional strict-open real frontier. Each component is
proved on a continuum, not extrapolated from sampled numerical evaluations. -/
namespace RHOnePrime.CMSWhole
open Real Set
open RHOnePrime.CMSScalar RHOnePrime.CMSPrime RHOnePrime.CMSOpen
set_option maxHeartbeats 0

lemma extend_margin {c d A B : ℝ} (hcd : c ≤ d)
    (hprev : ∀ L : ℝ, 44 ≤ L → L ≤ A → 0 < margin c L)
    (hnext : ∀ L : ℝ, A ≤ L → L ≤ B → 0 < margin d L) :
    ∀ L : ℝ, 44 ≤ L → L ≤ B → 0 < margin d L := by
  intro L hL hB
  by_cases hA : L ≤ A
  · exact (hprev L hL hA).trans_le (margin_mono_coefficient hcd (by linarith))
  · exact hnext L (by linarith) hB

theorem full_margin_083 : ∀ L : ℝ, 44 ≤ L → L ≤ 60 → 0 < margin (83 / 100) L := by
  intro L hL hB
  exact slab_083 hL hB

theorem full_margin_0844 : ∀ L : ℝ, 44 ≤ L → L ≤ 120 → 0 < margin (211 / 250) L := by
  exact extend_margin (c := (83 / 100 : ℝ)) (by norm_num) full_margin_083 (fun L hA hB => slab_0844 hA hB)

theorem full_margin_0856 : ∀ L : ℝ, 44 ≤ L → L ≤ 240 → 0 < margin (107 / 125) L := by
  exact extend_margin (c := (211 / 250 : ℝ)) (by norm_num) full_margin_0844 (fun L hA hB => slab_0856 hA hB)

theorem full_margin_0864 : ∀ L : ℝ, 44 ≤ L → L ≤ 480 → 0 < margin (108 / 125) L := by
  exact extend_margin (c := (107 / 125 : ℝ)) (by norm_num) full_margin_0856 (fun L hA hB => slab_0864 hA hB)

theorem full_margin_087 : ∀ L : ℝ, 44 ≤ L → L ≤ 960 → 0 < margin (87 / 100) L := by
  exact extend_margin (c := (108 / 125 : ℝ)) (by norm_num) full_margin_0864 (fun L hA hB => slab_087 hA hB)

theorem full_margin_0873 : ∀ L : ℝ, 44 ≤ L → L ≤ 1920 → 0 < margin (873 / 1000) L := by
  exact extend_margin (c := (87 / 100 : ℝ)) (by norm_num) full_margin_087 (fun L hA hB => slab_0873 hA hB)

theorem full_margin_0875 : ∀ L : ℝ, 44 ≤ L → L ≤ 3840 → 0 < margin (7 / 8) L := by
  exact extend_margin (c := (873 / 1000 : ℝ)) (by norm_num) full_margin_0873 (fun L hA hB => slab_0875 hA hB)

theorem full_margin_0876 : ∀ L : ℝ, 44 ≤ L → L ≤ 7680 → 0 < margin (219 / 250) L := by
  exact extend_margin (c := (7 / 8 : ℝ)) (by norm_num) full_margin_0875 (fun L hA hB => slab_0876 hA hB)

theorem full_margin_08765 : ∀ L : ℝ, 44 ≤ L → L ≤ 15360 → 0 < margin (1753 / 2000) L := by
  exact extend_margin (c := (219 / 250 : ℝ)) (by norm_num) full_margin_0876 (fun L hA hB => slab_08765 hA hB)

theorem open_prime_capped_ray (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {c B x : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1) (hB : 1 ≤ B)
    (hmargin : ∀ L : ℝ, 44 ≤ L → L ≤ B → 0 < margin c L)
    (hlo : exp 44 ≤ x) (hhi : x ≤ exp (B - 1)) :
    HasPrimeOpen x (x + (c + 1 / 10000) * sqrt x * log x) := by
  have hylo : exp 44 ≤ x + 1 := by linarith
  have hyhi : x + 1 ≤ exp B := by
    have h := shift_below_next_exp (by linarith : 0 ≤ B - 1) hhi
    simpa using h
  exact open_of_shifted_closed (by linarith) hc1 hlo
    (closed_prime_on_slab hCMS rh (by norm_num) hc hc1 hmargin hylo hyhi)

theorem open_capped_083 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 59) :
    HasPrimeOpen x (x + (8301 / 10000) * sqrt x * log x) := by
  have h := open_prime_capped_ray hCMS rh (c := (83 / 100 : ℝ)) (B := 60)
    (by norm_num) (by norm_num) (by norm_num) full_margin_083 hlo (by norm_num; exact hhi)
  norm_num at h ⊢
  exact h

theorem open_capped_0844 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 119) :
    HasPrimeOpen x (x + (8441 / 10000) * sqrt x * log x) := by
  have h := open_prime_capped_ray hCMS rh (c := (211 / 250 : ℝ)) (B := 120)
    (by norm_num) (by norm_num) (by norm_num) full_margin_0844 hlo (by norm_num; exact hhi)
  norm_num at h ⊢
  exact h

theorem open_capped_0856 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 239) :
    HasPrimeOpen x (x + (8561 / 10000) * sqrt x * log x) := by
  have h := open_prime_capped_ray hCMS rh (c := (107 / 125 : ℝ)) (B := 240)
    (by norm_num) (by norm_num) (by norm_num) full_margin_0856 hlo (by norm_num; exact hhi)
  norm_num at h ⊢
  exact h

theorem open_capped_0864 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 479) :
    HasPrimeOpen x (x + (8641 / 10000) * sqrt x * log x) := by
  have h := open_prime_capped_ray hCMS rh (c := (108 / 125 : ℝ)) (B := 480)
    (by norm_num) (by norm_num) (by norm_num) full_margin_0864 hlo (by norm_num; exact hhi)
  norm_num at h ⊢
  exact h

theorem open_capped_087 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 959) :
    HasPrimeOpen x (x + (8701 / 10000) * sqrt x * log x) := by
  have h := open_prime_capped_ray hCMS rh (c := (87 / 100 : ℝ)) (B := 960)
    (by norm_num) (by norm_num) (by norm_num) full_margin_087 hlo (by norm_num; exact hhi)
  norm_num at h ⊢
  exact h

theorem open_capped_0873 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 1919) :
    HasPrimeOpen x (x + (8731 / 10000) * sqrt x * log x) := by
  have h := open_prime_capped_ray hCMS rh (c := (873 / 1000 : ℝ)) (B := 1920)
    (by norm_num) (by norm_num) (by norm_num) full_margin_0873 hlo (by norm_num; exact hhi)
  norm_num at h ⊢
  exact h

theorem open_capped_0875 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 3839) :
    HasPrimeOpen x (x + (8751 / 10000) * sqrt x * log x) := by
  have h := open_prime_capped_ray hCMS rh (c := (7 / 8 : ℝ)) (B := 3840)
    (by norm_num) (by norm_num) (by norm_num) full_margin_0875 hlo (by norm_num; exact hhi)
  norm_num at h ⊢
  exact h

theorem open_capped_0876 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 7679) :
    HasPrimeOpen x (x + (8761 / 10000) * sqrt x * log x) := by
  have h := open_prime_capped_ray hCMS rh (c := (219 / 250 : ℝ)) (B := 7680)
    (by norm_num) (by norm_num) (by norm_num) full_margin_0876 hlo (by norm_num; exact hhi)
  norm_num at h ⊢
  exact h

theorem open_capped_08765 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 15359) :
    HasPrimeOpen x (x + (8766 / 10000) * sqrt x * log x) := by
  have h := open_prime_capped_ray hCMS rh (c := (1753 / 2000 : ℝ)) (B := 15360)
    (by norm_num) (by norm_num) (by norm_num) full_margin_08765 hlo (by norm_num; exact hhi)
  norm_num at h ⊢
  exact h

/-- A coefficient function on the full logarithmic ray. Values on overlapping
capped rays are chosen by the first applicable branch. No new kernel is claimed. -/
noncomputable def frontierCoefficient (L : ℝ) : ℝ :=
  if L ≤ 59 then 8301 / 10000 else
  if L ≤ 119 then 8441 / 10000 else
  if L ≤ 239 then 8561 / 10000 else
  if L ≤ 479 then 8641 / 10000 else
  if L ≤ 959 then 8701 / 10000 else
  if L ≤ 1919 then 8731 / 10000 else
  if L ≤ 3839 then 8751 / 10000 else
  if L ≤ 7679 then 8761 / 10000 else
  if L ≤ 15359 then 8766 / 10000 else
  8771 / 10000

theorem open_prime_frontier (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hx : exp 44 ≤ x) :
    HasPrimeOpen x (x + frontierCoefficient (log x) * sqrt x * log x) := by
  have hx0 : 0 < x := (exp_pos 44).trans_le hx
  unfold frontierCoefficient
  split_ifs with h0 h1 h2 h3 h4 h5 h6 h7 h8
  · exact open_capped_083 hCMS rh hx ((Real.log_le_iff_le_exp hx0).mp h0)
  · exact open_capped_0844 hCMS rh hx ((Real.log_le_iff_le_exp hx0).mp h1)
  · exact open_capped_0856 hCMS rh hx ((Real.log_le_iff_le_exp hx0).mp h2)
  · exact open_capped_0864 hCMS rh hx ((Real.log_le_iff_le_exp hx0).mp h3)
  · exact open_capped_087 hCMS rh hx ((Real.log_le_iff_le_exp hx0).mp h4)
  · exact open_capped_0873 hCMS rh hx ((Real.log_le_iff_le_exp hx0).mp h5)
  · exact open_capped_0875 hCMS rh hx ((Real.log_le_iff_le_exp hx0).mp h6)
  · exact open_capped_0876 hCMS rh hx ((Real.log_le_iff_le_exp hx0).mp h7)
  · exact open_capped_08765 hCMS rh hx ((Real.log_le_iff_le_exp hx0).mp h8)
  · exact open_prime_08771 hCMS rh hx

#print axioms open_capped_083
#print axioms open_capped_0844
#print axioms open_capped_0856
#print axioms open_capped_0864
#print axioms open_capped_087
#print axioms open_capped_0873
#print axioms open_capped_0875
#print axioms open_capped_0876
#print axioms open_capped_08765
#print axioms open_prime_frontier
#check @open_prime_frontier
end RHOnePrime.CMSWhole
