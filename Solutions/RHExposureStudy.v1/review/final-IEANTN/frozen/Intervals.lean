import FullRH
import IEANTN.Nodes.Buthe.v1.Conclusions
import OriginalPrimeInterval

open Real IEANTN
namespace IntervalStudy

/-- On the project's actual right-continuous functions, not a floor-relaxed
proxy: each prime in the difference of the inclusive finsets weighs at most log y. -/
theorem theta_diff_le_count {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    Chebyshev.theta y - Chebyshev.theta x ≤ (primeCounting y - primeCounting x)*log y := by
  let s := Nat.primesLE ⌊x⌋₊
  let t := Nat.primesLE ⌊y⌋₊
  have hs : s ⊆ t := Nat.primesLE_mono (Nat.floor_mono hxy)
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
  change (∑ p ∈ t, log (p : ℝ)) - (∑ p ∈ s, log (p : ℝ)) ≤ _
  have hd : (∑ p ∈ t \ s, log (p : ℝ)) = (∑ p ∈ t, log (p : ℝ)) -
      (∑ p ∈ s, log (p : ℝ)) := by
    linarith [Finset.sum_sdiff hs (f := fun p : ℕ ↦ log (p : ℝ))]
  rw [← hd]
  calc
    _ ≤ ∑ _p ∈ t \ s, log y := by
      apply Finset.sum_le_sum
      intro p hp
      have hpt := (Finset.mem_sdiff.mp hp).1
      have hp' := Nat.mem_primesLE.mp hpt
      apply Real.log_le_log (by exact_mod_cast hp'.2.pos)
      exact (Nat.cast_le.mpr hp'.1).trans (Nat.floor_le (by linarith))
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff_of_subset hs]
      rw [Nat.cast_sub (Finset.card_le_card hs)]
      simp only [s, t, Nat.primesLE_card_eq_primeCounting, primeCounting]

/-- Signed endpoint combination; no replacement of an error by its modulus. -/
theorem signed_count {x y u v : ℝ} (hx : 1 < x) (hxy : x ≤ y)
    (hxu : Chebyshev.theta x ≤ x - u) (hyv : y - v ≤ Chebyshev.theta y) :
    (y-x-v+u)/log y ≤ primeCounting y-primeCounting x := by
  have hl : 0 < log y := Real.log_pos (hx.trans_le hxy)
  apply (div_le_iff₀ hl).mpr
  linarith [theta_diff_le_count hx hxy]

theorem buthe_count (hlo : Buthe.v1.theorem_2_theta_lower)
    (hhi : Buthe.v1.theorem_2_theta) {x y : ℝ} (hx : 1423 ≤ x) (hy : y ≤ 10^19) (hxy : x ≤ y) :
    (y-x-1.95*sqrt y+0.05*sqrt x)/log y ≤ primeCounting y-primeCounting x := by
  apply signed_count (by linarith) hxy
  · linarith [hlo x (by linarith) (hxy.trans hy)]
  · linarith [hhi y (hx.trans hxy) hy]

theorem buthe_prime (hlo : Buthe.v1.theorem_2_theta_lower)
    (hhi : Buthe.v1.theorem_2_theta) {x y : ℝ} (hx : 1423 ≤ x) (hy : y ≤ 10^19) (hxy : x ≤ y)
    (hpos : 1.95*sqrt y-0.05*sqrt x < y-x) :
    HasPrimeInInterval x (y-x) := by
  have h1 := hlo x (by linarith) (hxy.trans hy)
  have h2 := hhi y (hx.trans hxy) hy
  apply (PrimeInterval.v1.Dev.theta_characterisation x (y-x)).mpr
  rw [show x+(y-x)=y by ring]
  linarith

#print axioms buthe_count
#print axioms buthe_prime
end IntervalStudy
