import ActualSourcePolynomial
namespace RHContinuation.Ramanujan
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier Ramanujan640.MainTerm
open Ramanujan640.Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def analyticError (u : ℝ) : ℝ :=
  tailNorm u+(11/5:ℝ)*(7*(Nat.factorial 21:ℝ)*u^17)+
    (7*(Nat.factorial 21:ℝ)*u^17)^2
noncomputable def scaledAnalyticError (u : ℝ) : ℝ :=
  (∑ j ∈ range 20, (tailCoeff j:ℝ)*u^(j+15))+
    (11/5:ℝ)*7*(Nat.factorial 21:ℝ)*u^15+
    (7*(Nat.factorial 21:ℝ))^2*u^32
lemma analyticError_scaled (u : ℝ) :
    analyticError u=u^2*scaledAnalyticError u := by
  unfold analyticError scaledAnalyticError tailNorm
  rw [mul_add,mul_add,Finset.mul_sum]
  have he : (∑ j ∈ range 20, (tailCoeff j:ℝ)*u^(j+17))=
      ∑ j ∈ range 20, u^2*((tailCoeff j:ℝ)*u^(j+15)) := by
    apply sum_congr rfl
    intro j hj
    rw [show j+17=2+(j+15) by omega,pow_add]
    ring
  rw [he]
  ring
lemma scaledAnalyticError_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    scaledAnalyticError u ≤ scaledAnalyticError v := by
  have ht : (∑ j ∈ range 20, (tailCoeff j:ℝ)*u^(j+15)) ≤
      ∑ j ∈ range 20, (tailCoeff j:ℝ)*v^(j+15) := by
    apply sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv _) (by positivity)
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv 15)
    (show 0 ≤ (11/5:ℝ)*7*(Nat.factorial 21:ℝ) by positivity)
  have hq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv 32)
    (sq_nonneg (7*(Nat.factorial 21:ℝ)))
  exact add_le_add (add_le_add ht hp) hq
lemma scaledAnalyticError_budget : scaledAnalyticError (1/60:ℝ) ≤ 1/2 := by
  norm_num [scaledAnalyticError,tailCoeff,Finset.sum_range_succ,Nat.factorial]
lemma analyticError_small {l : ℝ} (hl : 60 ≤ l) :
    analyticError (1/l) ≤ 1/(2*l^2) := by
  have hl0 : 0 < l := by linarith
  have hi : 1/l ≤ (1/60:ℝ) := one_div_le_one_div_of_le (by norm_num) hl
  have h := (scaledAnalyticError_mono (by positivity : 0 ≤ 1/l) hi).trans
    scaledAnalyticError_budget
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg (1/l))
  rw [analyticError_scaled]
  convert! hm using 1 <;> field_simp <;> ring

lemma coupled_dynamic_mainterm {u W V : ℝ} (hu : 0 < u) (hu26 : u ≤ 1/26)
    (hW0 : 0 ≤ W) (hW : W ≤ P u+7*(Nat.factorial 21:ℝ)*u^21)
    (hV : first u ≤ V) :
    difference u-analyticError u*u^4 ≤ V-W^2 := by
  let R : ℝ := 7*(Nat.factorial 21:ℝ)*u^21
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hP0 := P_nonneg hu.le
  have hP : P u ≤ 11/10 := (P_mono hu.le hu26).trans p20_budget
  have hu1 : u ≤ 1 := hu26.trans (by norm_num)
  have hu4 : 0 ≤ u^4 := by positivity
  have hu41 : u^4 ≤ 1 := by simpa using pow_le_pow_left₀ hu.le hu1 4
  let delta : ℝ := 7*(Nat.factorial 21:ℝ)*u^17
  have hR : R = delta*u^4 := by dsimp [R,delta]; ring
  have hRle : R ≤ delta*u^4 := hR.le
  have hcross : 2*P u*R ≤ (11/5:ℝ)*delta*u^4 := by
    have h1 := mul_le_mul_of_nonneg_right hP (show 0 ≤ 2*R by positivity)
    have h2 := mul_le_mul_of_nonneg_left hRle (by norm_num : (0:ℝ) ≤ 11/5)
    nlinarith
  have hsq : R^2 ≤ delta^2*u^4 := by
    have h1 := pow_le_pow_left₀ hR0 hRle 2
    have h2 := mul_nonneg (sq_nonneg delta)
      (mul_nonneg hu4 (sub_nonneg.mpr hu41))
    nlinarith
  have hWW : W^2 ≤ (P u+R)^2 := pow_le_pow_left₀ hW0 hW 2
  have htrunc := first_truncation hu.le (lt_of_le_of_lt hu26 (by norm_num))
  have hid := square_identity u
  have htail := mul_le_mul_of_nonneg_left (tail_mono hu.le hu26) hu4
  unfold analyticError
  change difference u-(tailNorm u+(11/5:ℝ)*delta+delta^2)*u^4 ≤ V-W^2
  nlinarith

theorem actual_dynamic_base {l : ℝ} (hl : 27 ≤ l) :
    l^4*sourcePolynomial (1/l)-analyticError (1/l) ≤ l^4*(l/(l-1)*RamStudy.w (l-1)-(RamStudy.w l)^2) := by
  have hl1 : 1 < l := by linarith
  have hl0 : 0 < l := by linarith
  have hu : 0 < 1/l := by positivity
  have hu26 : 1/l ≤ (1/26:ℝ) :=
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
  have h := mul_le_mul_of_nonneg_left (coupled_dynamic_mainterm hu hu26 hW0 hW hV)
    (show 0 ≤ l^4 by positivity)
  rw [sourcePolynomial_eq]
  simpa only [actual_w_eq] using (by
    convert! h using 1 <;> field_simp <;> ring :
      l^4*difference (1/l)-analyticError (1/l) ≤
        l^4*(l/(l-1)*w IEANTN.li (l-1)-(w IEANTN.li l)^2))


#print axioms actual_dynamic_base
#print axioms analyticError_small
end RHContinuation.Ramanujan
