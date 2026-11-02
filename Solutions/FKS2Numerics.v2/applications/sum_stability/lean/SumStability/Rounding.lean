import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-! Exact-value specification of finite binary64 and RN ties-even addition. -/
namespace SumStability

def u : ℚ := 1 / 2 ^ 53

def low : ℚ := 1 / 2 ^ 40

/-- All finite binary64 real values, with redundant dyadic encodings allowed. -/
def Binary64 (x : ℚ) : Prop :=
  ∃ m e : ℤ, |m| < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971 ∧ x = m * (2 : ℚ) ^ e

/-- Parity of the normalized significand, used only when a nearest result ties. -/
def EvenLSB (x : ℚ) : Prop :=
  x = 0 ∨
  (∃ m : ℤ, |m| < 2 ^ 52 ∧ x = m * (2 : ℚ) ^ (-1074 : ℤ) ∧ Even m) ∨
  ∃ m e : ℤ, 2 ^ 52 ≤ |m| ∧ |m| < 2 ^ 53 ∧
    -1074 ≤ e ∧ e ≤ 971 ∧ x = m * (2 : ℚ) ^ e ∧ Even m

/-- Correct rounding is specified by nearest representable value, with even tie-breaking.
No forward-error property is part of this primitive's definition. -/
def RN64 (x y : ℚ) : Prop :=
  Binary64 y ∧ (∀ z, Binary64 z → |y - x| ≤ |z - x|) ∧
    ((∃ z, Binary64 z ∧ z ≠ y ∧ |z - x| = |y - x|) → EvenLSB y)

/-- Integer RN ties-even, for constructing a nearby representable value. -/
def rne (x : ℚ) : ℤ :=
  let m := ⌊x⌋
  if x - m < 1 / 2 then m
  else if x - m > 1 / 2 then m + 1
  else if m % 2 = 0 then m else m + 1

theorem rne_error (x : ℚ) : |(rne x : ℚ) - x| ≤ 1 / 2 := by
  have h₁ := Int.floor_le x
  have h₂ := Int.lt_floor_add_one x
  simp only [rne]
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

theorem rne_bounds (x : ℚ) (a b : ℤ) (ha : (a : ℚ) ≤ x) (hb : x ≤ b) :
    a ≤ rne x ∧ rne x ≤ b := by
  have h₁ := Int.floor_le x
  have h₂ := Int.lt_floor_add_one x
  have h₃ : a ≤ ⌊x⌋ := Int.le_floor.mpr ha
  have h₄ : ⌊x⌋ ≤ b := by exact_mod_cast (h₁.trans hb)
  simp only [rne]
  split_ifs <;> constructor
  all_goals first | omega | skip
  all_goals
    have he : ⌊x⌋ < b := by
      by_contra hh
      have : ⌊x⌋ = b := by omega
      simp_all
      linarith
    omega

theorem binade_cover (N : ℕ) (x : ℚ) (hx : low ≤ x)
    (hN : x ≤ low * 2 ^ N) :
    ∃ k ≤ N, low * 2 ^ k ≤ x ∧ x ≤ 2 * (low * 2 ^ k) := by
  induction N with
  | zero => exact ⟨0, le_refl _, by simpa using hx, by simpa using hN.trans (by
      dsimp [low]; norm_num)⟩
  | succ N ih =>
    by_cases h : x ≤ low * 2 ^ N
    · obtain ⟨k, hk, hl, hu⟩ := ih h
      exact ⟨k, Nat.le_succ_of_le hk, hl, hu⟩
    · exact ⟨N, Nat.le_succ _, le_of_lt (lt_of_not_ge h), by
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hN⟩

/-- Normalization of a grid point, including a carry across a binade boundary. -/
theorem grid_binary64 (k : ℕ) (hk : k ≤ 47) (m : ℤ)
    (hm : 2 ^ 52 ≤ m ∧ m ≤ 2 ^ 53) :
    Binary64 ((m : ℚ) * ((low * 2 ^ k) / 2 ^ 52)) := by
  have he : (low * (2 : ℚ) ^ k) / 2 ^ 52 = (2 : ℚ) ^ ((k : ℤ) - 92) := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast]
    norm_num [low]
    ring
  rw [he]
  by_cases htop : m = 2 ^ 53
  · refine ⟨2 ^ 52, (k : ℤ) - 91, by norm_num, by omega, by omega, ?_⟩
    subst m
    have hpow : (2 : ℚ) ^ ((k : ℤ) - 91) =
        2 * (2 : ℚ) ^ ((k : ℤ) - 92) := by
      have : (k : ℤ) - 91 = (k : ℤ) - 92 + 1 := by omega
      rw [this, zpow_add₀ (by norm_num)]
      norm_num
      ring
    rw [hpow]
    norm_num
    ring
  · exact ⟨m, (k : ℤ) - 92, by rw [abs_of_nonneg (by omega)]; omega,
      by omega, by omega, rfl⟩

theorem rn_exact {x y : ℚ} (hx : Binary64 x) (h : RN64 x y) : y = x := by
  have := h.2.1 x hx
  simpa only [sub_self, abs_zero, abs_nonpos_iff, sub_eq_zero] using this

/-- A proved normal-range relative bound, obtained from nearestness and a grid witness. -/
theorem rn_relative {x y : ℚ} (hx : low ≤ x) (hhi : x ≤ 128) (h : RN64 x y) :
    |y - x| ≤ u * x := by
  obtain ⟨k, hk, hl, hu⟩ := binade_cover 47 x hx (by norm_num [low]; exact hhi)
  let p : ℚ := low * 2 ^ k
  let d : ℚ := p / 2 ^ 52
  have hp : 0 < p := by dsimp [p, low]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hs : (2 ^ 52 : ℚ) ≤ x / d ∧ x / d ≤ 2 ^ 53 := by
    dsimp [d]
    constructor
    · apply (le_div_iff₀ (by positivity)).mpr
      have : (2 ^ 52 : ℚ) * (p / 2 ^ 52) = p := by ring
      rwa [this]
    · apply (div_le_iff₀ (by positivity)).mpr
      have : (2 ^ 53 : ℚ) * (p / 2 ^ 52) = 2 * p := by norm_num; ring
      rwa [this]
  have hm := rne_bounds (x / d) (2 ^ 52) (2 ^ 53) (by norm_num; exact hs.1)
    (by norm_num; exact hs.2)
  have hb := grid_binary64 k hk (rne (x / d)) hm
  have hn := h.2.1 _ hb
  have hg : |(rne (x / d) : ℚ) * d - x| ≤ d / 2 := by
    have ht := mul_le_mul_of_nonneg_right (rne_error (x / d)) hd.le
    have he : ((rne (x / d) : ℚ) - x / d) * d = (rne (x / d) : ℚ) * d - x := by
      field_simp
    have ht' : |((rne (x / d) : ℚ) - x / d) * d| ≤ (1 / 2) * d := by
      simpa only [abs_mul, abs_of_pos hd] using ht
    rw [he] at ht'
    linarith
  have hu' : d / 2 = u * p := by dsimp [d, u]; norm_num; ring
  exact hn.trans (hg.trans (by rw [hu']; exact mul_le_mul_of_nonneg_left hl (by
    norm_num [u])))

theorem rn_delta {x y : ℚ} (hx : low ≤ x) (hhi : x ≤ 128) (h : RN64 x y) :
    ∃ δ : ℚ, |δ| ≤ u ∧ y = x * (1 + δ) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num [low]) hx
  refine ⟨(y - x) / x, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hxpos]
    exact (div_le_iff₀ hxpos).mpr (rn_relative hx hhi h)
  · field_simp
    ring

end SumStability
