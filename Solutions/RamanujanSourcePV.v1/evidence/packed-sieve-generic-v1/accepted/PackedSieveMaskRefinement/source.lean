/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveGeometric

/-! Exact refinement of one finite packed stride to the existing complete
segmented-checker divisibility predicate. No prime list or bit label is assumed. -/
namespace RamanujanPV.PackedSieveMaskRefinement
open PackedSieveKernel PackedSieveGeometric SegmentCheckerMath
set_option autoImplicit false
set_option maxHeartbeats 0

theorem testBit_shifted_geom (p m shift i : Nat) (hp : 0 < p) :
    (Nat.shiftLeft (geomMask p m) shift).testBit i = true ↔
      ∃ k < m, i = shift + k * p := by
  rw [Nat.shiftLeft_eq', Nat.testBit_shiftLeft]
  simp only [Bool.and_eq_true, decide_eq_true_eq, testBit_geomMask p m (i-shift) hp]
  constructor
  · rintro ⟨hle, k, hk, heq⟩
    exact ⟨k, hk, by omega⟩
  · rintro ⟨k, hk, heq⟩
    refine ⟨by omega, k, hk, ?_⟩
    omega

theorem divisorMask_visited {lo hi p n : Nat} (hp : 0 < p)
    (hlo : lo ≤ n) (hhi : n ≤ hi) :
    (divisorMask lo hi p).testBit (n-lo) = true ↔
      Visited (firstMultiple lo p) p (markCount lo hi p) n := by
  have hfirstLo := (first_lower (lo := lo) hp).1
  by_cases hfirst : firstMultiple lo p ≤ hi
  · simp only [divisorMask, if_pos hfirst, testBit_shifted_geom _ _ _ _ hp,
      Visited, markCount, if_pos hfirst]
    constructor
    · rintro ⟨k, hk, hvalue⟩
      exact ⟨k, hk, by omega⟩
    · rintro ⟨k, hk, hvalue⟩
      exact ⟨k, hk, by omega⟩
  · simp [divisorMask, hfirst, Visited, markCount]

theorem divisorMask_sound_complete {lo hi p n : Nat} (hp : 0 < p)
    (hlo : lo ≤ n) (hhi : n ≤ hi) :
    (divisorMask lo hi p).testBit (n-lo) = true ↔ p*p ≤ n ∧ p ∣ n := by
  rw [divisorMask_visited hp hlo hhi]
  exact visited_iff hp hlo hhi

#print axioms testBit_shifted_geom
#print axioms divisorMask_visited
#print axioms divisorMask_sound_complete
end RamanujanPV.PackedSieveMaskRefinement
