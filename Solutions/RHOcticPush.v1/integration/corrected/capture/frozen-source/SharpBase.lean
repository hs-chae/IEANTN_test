import ActualSourcePolynomial

/-! The old degree20 C-coefficient provider is unchanged. Tighten only the
analytically justified square/remainder budget on its actual domainL≥27. -/
namespace RHOcticPush.SharpBase
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier Ramanujan640.MainTerm
open Ramanujan640.Polynomial RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def delta27 : ℝ := 7*(Nat.factorial 21:ℝ)/27^17

lemma square_tail_budget27 :
    tailNorm (1/27:ℝ)+(11/5:ℝ)*delta27+delta27^2 ≤ 3/8000 := by
  norm_num [tailNorm,tailCoeff,delta27,Finset.sum_range_succ,Nat.factorial]

lemma p20_budget27 : P (1/27:ℝ) ≤ 11/10 := by
  norm_num [P,Finset.sum_range_succ,Nat.factorial]

noncomputable def sharpBase (z : ℝ) : ℝ :=
  z^4*sourcePolynomial (1/z)-3/8000

lemma sharpBase_identity {z : ℝ} (hz : z ≠ 0) :
    sharpBase z = z^4*difference (1/z)-3/8000 := by
  unfold sharpBase
  rw [sourcePolynomial_eq]

lemma sharpBase_eq_full {z : ℝ} (hz : z ≠ 0) :
    sharpBase z = fullBase z+1/1600 := by
  rw [sharpBase_identity hz,fullBase_identity hz]
  ring

lemma coupled_tight_mainterm {u W V : ℝ} (hu : 0 < u) (hu27 : u ≤ 1/27)
    (hW0 : 0 ≤ W) (hW : W ≤ P u+7*(Nat.factorial 21:ℝ)*u^21)
    (hV : first u ≤ V) :
    difference u-(3/8000:ℝ)*u^4 ≤ V-W^2 := by
  let R : ℝ := 7*(Nat.factorial 21:ℝ)*u^21
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hP0 := P_nonneg hu.le
  have hP : P u ≤ 11/10 := (P_mono hu.le hu27).trans p20_budget27
  have hu1 : u ≤ 1 := hu27.trans (by norm_num)
  have hu4 : 0 ≤ u^4 := by positivity
  have hu41 : u^4 ≤ 1 := by simpa using pow_le_pow_left₀ hu.le hu1 4
  have hR : R ≤ delta27*u^4 := by
    have hp := pow_le_pow_left₀ hu.le hu27 17
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (show 0 ≤ 7*(Nat.factorial 21:ℝ) by positivity)) hu4
    convert! hm using 1 <;> dsimp [R,delta27] <;> norm_num <;> ring
  have hcross : 2*P u*R ≤ (11/5:ℝ)*delta27*u^4 := by
    have h1 := mul_le_mul_of_nonneg_right hP (show 0 ≤ 2*R by positivity)
    have h2 := mul_le_mul_of_nonneg_left hR (by norm_num : (0:ℝ) ≤ 11/5)
    nlinarith
  have hsq : R^2 ≤ delta27^2*u^4 := by
    have h1 := pow_le_pow_left₀ hR0 hR 2
    have h2 := mul_nonneg (sq_nonneg delta27)
      (mul_nonneg hu4 (sub_nonneg.mpr hu41))
    nlinarith
  have hWW : W^2 ≤ (P u+R)^2 := pow_le_pow_left₀ hW0 hW 2
  have htrunc := first_truncation hu.le (lt_of_le_of_lt hu27 (by norm_num))
  have hid := square_identity u
  have htail := mul_le_mul_of_nonneg_left (tail_mono hu.le hu27) hu4
  have hbudget := mul_le_mul_of_nonneg_left square_tail_budget27 hu4
  nlinarith

theorem actual_sharp_base {l : ℝ} (hl : 27 ≤ l) :
    sharpBase l ≤ l^4*(l/(l-1)*RamStudy.w (l-1)-(RamStudy.w l)^2) := by
  have hl1 : 1 < l := by linarith
  have hl0 : 0 < l := by linarith
  have hu : 0 < 1/l := by positivity
  have hu27 : 1/l ≤ (1/27:ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hw := actual_factorial_barrier26 (z:=l) (by linarith)
  have hv := actual_factorial_barrier26 (z:=l-1) (by linarith)
  have hPN : 0 ≤ pN 20 l := by unfold pN; positivity
  have hW0 : 0 ≤ w IEANTN.li l := hPN.trans hw.1
  have hW : w IEANTN.li l ≤ P (1/l)+7*(Nat.factorial 21:ℝ)*(1/l)^21 := by
    rw [P_inv]
    simpa [one_div_pow,div_eq_mul_inv,mul_assoc] using hw.2
  have hV : first (1/l) ≤ l/(l-1)*w IEANTN.li (l-1) := by
    rw [first_inv hl1]
    exact mul_le_mul_of_nonneg_left hv.1 (by positivity)
  have h := mul_le_mul_of_nonneg_left (coupled_tight_mainterm hu hu27 hW0 hW hV)
    (show 0 ≤ l^4 by positivity)
  rw [sharpBase_identity (ne_of_gt hl0)]
  simpa only [actual_w_eq] using (by
    convert! h using 1 <;> field_simp <;> ring :
      l^4*difference (1/l)-3/8000 ≤
        l^4*(l/(l-1)*w IEANTN.li (l-1)-(w IEANTN.li l)^2))


#print axioms square_tail_budget27
#print axioms actual_sharp_base
end RHOcticPush.SharpBase
