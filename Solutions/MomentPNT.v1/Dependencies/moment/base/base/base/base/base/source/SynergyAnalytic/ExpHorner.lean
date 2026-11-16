import Mathlib
namespace SynergyAnalytic
open Real Finset
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- The real counterpart of the descending divided-Horner loop:
start at 1 and apply p := 1-z*p/i for i=48,...,1. -/
noncomputable def expHorner : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 1
  | n+1, k, z => 1-z/(k+1)*expHorner n (k+1) z

noncomputable def expTaylor48 (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 49, (-z)^i/(i.factorial:ℝ)

theorem expHorner48_eq (z : ℝ) : expHorner 48 0 z = expTaylor48 z := by
  norm_num [expHorner,expTaylor48,Finset.sum_range_succ]
  ring

/-- A single128-bit fixed-point quantum is more than the complete analytic
degree48 remainder on the reduced interval. Directed arithmetic rounding is
separate and must be proved by the source implementation. -/
theorem exp_neg_unit_horner_error {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    |Real.exp (-z)-expHorner 48 0 z| ≤ 1/(2:ℝ)^128 := by
  have habs : |(-z:ℝ)| ≤ 1 := by rw [abs_neg,abs_of_nonneg hz];exact hz1
  have hb := Real.exp_bound habs (n:=49) (by decide)
  have hpow : |(-z:ℝ)|^49 ≤ 1 := pow_le_one₀ (abs_nonneg _) habs
  have hp := mul_le_mul_of_nonneg_right hpow
    (show 0 ≤ (50:ℝ)/((49).factorial*49) by positivity)
  have hnum : (50:ℝ)/((49).factorial*49) ≤ 1/(2:ℝ)^128 := by norm_num [Nat.factorial]
  have hp' : |(-z:ℝ)|^49*((50:ℝ)/((49).factorial*49)) ≤ (50:ℝ)/((49).factorial*49) := by
    simpa only [one_mul] using hp
  rw [expHorner48_eq]
  exact hb.trans (hp'.trans hnum)

theorem exp_neg_unit_horner_bounds {z lo hi : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hl : lo ≤ expHorner 48 0 z) (hu : expHorner 48 0 z ≤ hi) :
    lo-1/(2:ℝ)^128 ≤ Real.exp (-z) ∧ Real.exp (-z) ≤ hi+1/(2:ℝ)^128 := by
  have hh := abs_le.mp (exp_neg_unit_horner_error hz hz1)
  constructor <;> linarith

theorem exp_neg_scale64 (x : ℝ) : (Real.exp (-(x/64)))^64 = Real.exp (-x) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- A real interval supplied by the source arithmetic remains valid after the
six source squarings. Application storage and unsigned overflow are not assumed. -/
theorem exp_neg_64_horner_bounds {x lo hi : ℝ} (hx : 0 ≤ x) (hx64 : x ≤ 64)
    (hl : lo ≤ expHorner 48 0 (x/64)) (hu : expHorner 48 0 (x/64) ≤ hi) :
    (max 0 (lo-1/(2:ℝ)^128))^64 ≤ Real.exp (-x) ∧
      Real.exp (-x) ≤ (hi+1/(2:ℝ)^128)^64 := by
  have hh := exp_neg_unit_horner_bounds (by positivity : (0:ℝ)≤x/64)
    (by linarith : x/64≤1) hl hu
  have hlo : max 0 (lo-1/(2:ℝ)^128) ≤ Real.exp (-(x/64)) :=
    max_le (Real.exp_pos _).le hh.1
  have h1 := pow_le_pow_left₀ (le_max_left (0:ℝ) _) hlo 64
  have h2 := pow_le_pow_left₀ (Real.exp_pos _).le hh.2 64
  rw [exp_neg_scale64] at h1 h2
  exact ⟨h1,h2⟩

#print axioms exp_neg_unit_horner_error
#print axioms exp_neg_64_horner_bounds
end SynergyAnalytic
