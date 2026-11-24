import BoxIntegratedDefs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Actual trivial-zero primitive series, with its derivative evaluated by the
convergent Mercator series on the precise physical domain x>1. -/
namespace RHOcticPush.BoxPerron
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def trivialDerivative (n : ℕ) (x : ℝ) : ℝ :=
  -(x^(-2 : ℤ))^(n+1)/(2*((n+1 : ℕ) : ℝ))

lemma trivialPrimitive_hasDerivAt (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (trivialPrimitive n) (trivialDerivative n x) x := by
  have hd := (hasDerivAt_zpow ((1:ℤ)-2*((n+1:ℕ):ℤ)) x (Or.inl hx)).div_const
    ((2*((n+1:ℕ):ℝ))*(2*((n+1:ℕ):ℝ)-1))
  convert hd using 1 <;> try rfl
  dsimp [trivialDerivative]
  have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have he : ((1:ℤ)-2*((n+1:ℕ):ℤ))-1=(-2:ℤ)*((n+1:ℕ):ℤ) := by ring
  simp only [Nat.cast_add, Nat.cast_one] at he
  rw [he, zpow_mul, show ((n : ℤ) + 1) = ((n+1 : ℕ) : ℤ) by norm_num,
    zpow_natCast]
  push_cast
  have hden : (2*((n:ℝ)+1)-1) ≠ 0 := by
    have hn0 : (0:ℝ) ≤ n := by positivity
    nlinarith
  field_simp [hden]
  <;> ring

lemma trivialDerivative_hasSum {x : ℝ} (hx : 1 < x) :
    HasSum (fun n => trivialDerivative n x) (-IEANTN.RHSmoothing.trivial x) := by
  have hx0 : 0 < x := by linarith
  have hq0 : 0 ≤ x^(-2 : ℤ) := zpow_nonneg hx0.le _
  have hq1 : x^(-2 : ℤ) < 1 := by
    simp only [zpow_neg, zpow_ofNat]
    exact inv_lt_one_of_one_lt₀ (by nlinarith)
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one (x := x^(-2 : ℤ))
    (by simpa only [abs_of_nonneg hq0] using hq1)).mul_left (-1/2 : ℝ)
  convert h using 1 <;> try rfl
  · funext n
    dsimp [trivialDerivative]
    push_cast
    field_simp <;> ring
  · unfold IEANTN.RHSmoothing.trivial
    ring

lemma inverse_square_lt_one {x : ℝ} (hx : 1 < x) : x^(-2 : ℤ) < 1 := by
  simp only [zpow_neg, zpow_ofNat]
  exact inv_lt_one_of_one_lt₀ (by nlinarith)

lemma trivialPrimitive_eq_power (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    trivialPrimitive n x = x*(x^(-2 : ℤ))^(n+1) /
      ((2*((n+1 : ℕ):ℝ))*(2*((n+1 : ℕ):ℝ)-1)) := by
  unfold trivialPrimitive
  congr 1
  rw [show (1:ℤ)-2*((n+1:ℕ):ℤ)=1+(-2)*((n+1:ℕ):ℤ) by ring,
    zpow_add₀ hx, zpow_one, zpow_mul, zpow_natCast]

lemma trivialPrimitive_bound (n : ℕ) {x : ℝ} (hx : 1 < x) :
    ‖trivialPrimitive n x‖ ≤ x*(x^(-2 : ℤ))^(n+1) := by
  rw [trivialPrimitive_eq_power n (by linarith : x ≠ 0)]
  have hn : (1 : ℝ) ≤ ((n+1 : ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hp : 0 ≤ x*(x^(-2 : ℤ))^(n+1) := by positivity
  have hd : 1 ≤ (2*((n+1 : ℕ):ℝ))*(2*((n+1 : ℕ):ℝ)-1) := by nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hp (by linarith))]
  exact div_le_self hp hd

theorem trivialPrimitive_summable {x : ℝ} (hx : 1 < x) :
    Summable (fun n => trivialPrimitive n x) := by
  have hq0 : 0 ≤ x^(-2 : ℤ) := zpow_nonneg (by linarith) _
  have hg := summable_geometric_of_abs_lt_one
    (show |x^(-2 : ℤ)| < 1 by rw [abs_of_nonneg hq0]; exact inverse_square_lt_one hx)
  exact (((summable_nat_add_iff 1).mpr hg).mul_left x).of_norm_bounded
    (fun n => trivialPrimitive_bound n hx)

lemma trivialDerivative_uniform {a x : ℝ} (ha : 1 < a) (hax : a ≤ x) (n : ℕ) :
    ‖trivialDerivative n x‖ ≤ (a^(-2 : ℤ))^(n+1) := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := ha0.trans_le hax
  have hq : x^(-2 : ℤ) ≤ a^(-2 : ℤ) := by
    simp only [zpow_neg, zpow_ofNat]
    exact inv_anti₀ (sq_pos_of_pos ha0) (pow_le_pow_left₀ ha0.le hax 2)
  unfold trivialDerivative
  rw [norm_div, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (zpow_nonneg hx0.le _) _),
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*((n+1:ℕ):ℝ))]
  calc
    _ ≤ (x^(-2 : ℤ))^(n+1) := div_le_self (by positivity) (by
      have : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      linarith)
    _ ≤ _ := pow_le_pow_left₀ (zpow_nonneg hx0.le _) hq _

/-- Differentiation of the COMPLETE actual trivial-zero primitive series. -/
theorem trivialTSum_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y => ∑' n, trivialPrimitive n y) (-IEANTN.RHSmoothing.trivial x) x := by
  let a := (x+1)/2
  have ha : 1 < a := by dsimp [a]; linarith
  have hax : a < x := by dsimp [a]; linarith
  have hq0 : 0 ≤ a^(-2 : ℤ) := zpow_nonneg (by linarith) _
  have hg := summable_geometric_of_abs_lt_one
    (show |a^(-2 : ℤ)| < 1 by rw [abs_of_nonneg hq0]; exact inverse_square_lt_one ha)
  have hd := hasDerivAt_tsum_of_isPreconnected
    ((summable_nat_add_iff 1).mpr hg) isOpen_Ioi (convex_Ioi a).isPreconnected
    (fun n y hy => trivialPrimitive_hasDerivAt n (by have hy1 : 1 < y := ha.trans hy; linarith))
    (fun n y hy => trivialDerivative_uniform ha hy.le n)
    hax (trivialPrimitive_summable hx) hax
  simpa only [(trivialDerivative_hasSum hx).tsum_eq] using hd

#print axioms trivialPrimitive_hasDerivAt
#print axioms trivialDerivative_hasSum
#print axioms trivialPrimitive_summable
#print axioms trivialTSum_hasDerivAt
end RHOcticPush.BoxPerron
