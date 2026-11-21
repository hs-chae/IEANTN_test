import Anchor640
import Polynomial640

namespace Ramanujan640.MainTerm
open Real Set Finset RamanujanPV.AnalyticTransition
open Ramanujan640.AnalyticBarrier Ramanujan640.Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def delta : ℝ := 7*(Nat.factorial 21:ℝ)/26^17

theorem square_tail_budget :
    tailNorm (1/26:ℝ)+(11/5:ℝ)*delta+delta^2 ≤ 1/1000 := by
  norm_num [tailNorm,tailCoeff,delta,Finset.sum_range_succ,Nat.factorial]

theorem p20_budget : P (1/26:ℝ) ≤ 11/10 := by
  norm_num [P,Finset.sum_range_succ,Nat.factorial]

lemma P_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ P u := by
  unfold P
  positivity

lemma P_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : P u ≤ P v := by
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv _) (by positivity)

/-- Complete degree20 coupled estimate, including both omitted square
coefficients and the true factorial remainder. -/
theorem coupled_mainterm {u W V : ℝ} (hu : 0 < u) (hu26 : u ≤ 1/26)
    (hW0 : 0 ≤ W) (hW : W ≤ P u+7*(Nat.factorial 21:ℝ)*u^21)
    (hV : first u ≤ V) :
    1+14*u+145*u^2+1412*u^3-1/1000 ≤ (V-W^2)/u^4 := by
  let R : ℝ := 7*(Nat.factorial 21:ℝ)*u^21
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hP0 := P_nonneg hu.le
  have hP : P u ≤ 11/10 := (P_mono hu.le hu26).trans p20_budget
  have hu1 : u ≤ 1 := hu26.trans (by norm_num)
  have hu4 : 0 ≤ u^4 := by positivity
  have hu41 : u^4 ≤ 1 := by
    simpa using pow_le_pow_left₀ hu.le hu1 4
  have hR : R ≤ delta*u^4 := by
    have hp := pow_le_pow_left₀ hu.le hu26 17
    have hc : 0 ≤ 7*(Nat.factorial 21:ℝ) := by positivity
    have hm := mul_le_mul_of_nonneg_left hp hc
    have hm2 := mul_le_mul_of_nonneg_right hm hu4
    convert! hm2 using 1 <;> dsimp [R,delta] <;> norm_num <;> ring
  have hcross : 2*P u*R ≤ (11/5:ℝ)*delta*u^4 := by
    have h1 := mul_le_mul_of_nonneg_right hP (show 0 ≤ 2*R by positivity)
    have h2 := mul_le_mul_of_nonneg_left hR (by norm_num : (0:ℝ) ≤ 11/5)
    nlinarith
  have hsq : R^2 ≤ delta^2*u^4 := by
    have h1 := pow_le_pow_left₀ hR0 hR 2
    have h2 := mul_nonneg (sq_nonneg delta) (mul_nonneg hu4 (sub_nonneg.mpr hu41))
    nlinarith
  have hWW : W^2 ≤ (P u+R)^2 :=
    pow_le_pow_left₀ hW0 hW 2
  have hpoly := base_polynomial_lower hu.le (lt_of_le_of_lt hu26 (by norm_num))
  have htail := mul_le_mul_of_nonneg_left (tail_mono hu.le hu26) hu4
  have hbudget := mul_le_mul_of_nonneg_left square_tail_budget hu4
  apply (le_div_iff₀ (pow_pos hu 4)).2
  nlinarith

lemma P_inv (l : ℝ) : P (1/l) = pN 20 l := by
  unfold P pN
  apply Finset.sum_congr rfl
  intro k hk
  simp [one_div_pow,div_eq_mul_inv]

lemma first_inv {l : ℝ} (hl : 1 < l) :
    first (1/l) = l/(l-1)*pN 20 (l-1) := by
  have hl0 : l ≠ 0 := by linarith
  have hl1 : l-1 ≠ 0 := by linarith
  have hid : 1-1/l = (l-1)/l := by field_simp <;> ring
  unfold first pN
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hid]
  simp only [div_pow,one_pow,pow_succ]
  field_simp
  <;> ring

/-- The actual li-only lower envelope from the locked900s draft.
All numerical anchors, polynomial signs and tail charges have been proved;
only the precise standard li series/derivative identities remain inputs. -/
theorem actual_mainterm_lower {li : ℝ → ℝ}
    (hseries : LogIntegralSeriesIdentity li) (hderiv : LogIntegralDerivative li)
    {l : ℝ} (hl : 27 ≤ l) :
    1+14/l+145/l^2+1412/l^3-1/1000 ≤
      l^4*(l/(l-1)*w li (l-1)-(w li l)^2) := by
  have hl1 : 1 < l := by linarith
  have hl0 : 0 < l := by linarith
  have hlm : 0 < l-1 := by linarith
  have hu : 0 < 1/l := by positivity
  have hu26 : 1/l ≤ (1/26:ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num : (0:ℝ)<26) (by linarith)
  have hw := factorial_barrier26 hseries hderiv (z:=l) (by linarith)
  have hv := factorial_barrier26 hseries hderiv (z:=l-1) (by linarith)
  have hPN : 0 ≤ pN 20 l := by unfold pN; positivity
  have hW0 : 0 ≤ w li l := hPN.trans hw.1
  have hW : w li l ≤ P (1/l)+7*(Nat.factorial 21:ℝ)*(1/l)^21 := by
    rw [P_inv]
    simpa [one_div_pow,div_eq_mul_inv,mul_assoc] using hw.2
  have hV : first (1/l) ≤ l/(l-1)*w li (l-1) := by
    rw [first_inv hl1]
    exact mul_le_mul_of_nonneg_left hv.1 (by positivity)
  have h := coupled_mainterm hu hu26 hW0 hW hV
  convert! h using 1 <;> simp only [one_div_pow] <;> field_simp <;> ring

#print axioms square_tail_budget
#print axioms coupled_mainterm
#print axioms actual_mainterm_lower
end Ramanujan640.MainTerm
