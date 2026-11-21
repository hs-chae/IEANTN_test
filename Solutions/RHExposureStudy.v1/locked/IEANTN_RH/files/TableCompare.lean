import FullRH
import Numerics
import RamanujanPV.AnalyticTransition

open Real IEANTN
open DudekPlattNumerics.v4.Numerics (poly_exp_decreasing)
namespace TableCompare
set_option maxRecDepth 5000
set_option maxHeartbeats 0

theorem exp_neg_nat (n : ℕ) : exp (-(n:ℝ)) ≤ (1000/2718:ℝ)^n := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2718/1000)
    (show (2718/1000:ℝ) ≤ exp 1 by linarith [exp_one_gt_d9]) n
  rw [exp_one_pow] at hp
  rw [exp_neg, ← one_div, ← show (1:ℝ)/(2718/1000)=1000/2718 by norm_num,
    one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) hp

theorem uniform_offset_error (hRH : SharedRH.hypothesis)
    (hb : Buthe2016.v1.theorem_2_li_minus_pi)
    (hoff : RamanujanPV.Middle.LiOffsetIdentity)
    (hc : |li 2| ≤ (2:ℝ)) {x : ℝ} (hx : exp 330 ≤ x) :
    Eπ x < (10:ℝ)^(-68:ℤ) := by
  let L := log x
  have hx0 : 0 < x := (exp_pos 330).trans_le hx
  have hL : 330 ≤ L := by simpa [L] using log_le_log (exp_pos 330) hx
  have h60 : (2657:ℝ) < x := by
    have h0 : exp (9:ℝ) ≤ x := (exp_le_exp.mpr (by norm_num)).trans hx
    have he := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10)
      (show (27/10:ℝ) ≤ exp 1 by linarith [exp_one_gt_d9]) 9
    rw [exp_one_pow] at he
    norm_num at he
    linarith
  have hp := FullRH.buthe_all_pi hRH hb h60
  have hf : primeCounting x - Li x = (primeCounting x - li x) + li 2 := by
    rw [hoff x (by linarith)]; ring
  have hd := (abs_add_le (primeCounting x - li x) (li 2)).trans
    (add_le_add hp hc)
  have hraw : Eπ x ≤ (1/(8*π))*(L^2*exp (-L/2)) + 2*(L*exp (-L)) := by
    unfold Eπ
    rw [hf]
    calc
      _ ≤ (sqrt x * log x/(8*π)+2)/(x/log x) :=
        div_le_div_of_nonneg_right hd (div_nonneg hx0.le (by linarith))
      _ = _ := by
        have hlog : 0 < log x := by linarith
        have hxexp := exp_log hx0
        dsimp only [L]
        rw [show -log x/2 = -(log x/2) by ring,exp_neg,exp_neg,Real.exp_half,exp_log hx0]
        field_simp [hlog.ne',hx0.ne',pi_ne_zero,show sqrt x ≠ 0 by positivity]
        linear_combination (log x) * (Real.mul_self_sqrt hx0.le)
  have h1 := poly_exp_decreasing 2 (L0 := (330:ℝ)) (c := (1/2:ℝ)) (by norm_num) (by norm_num) hL
  have h1' : L^2*exp (-L/2) ≤ (330:ℝ)^2*exp (-165) := by
    convert h1 using 1 <;> congr 1 <;> ring
  have h2 := poly_exp_decreasing 1 (L0 := (330:ℝ)) (c := (1:ℝ)) (by norm_num) (by norm_num) hL
  have h2' : L*exp (-L) ≤ (330:ℝ)*exp (-330) := by simpa using h2
  have h165 : exp (-165:ℝ) ≤ (1000/2718:ℝ)^165 := by simpa using exp_neg_nat 165
  have h330 : exp (-330:ℝ) ≤ (1000/2718:ℝ)^330 := by simpa using exp_neg_nat 330
  have hi : 1/(8*π) ≤ 1/(8*3.14:ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [pi_gt_d2])
  have f1 : (1/(8*3.14:ℝ))*((330:ℝ)^2*(1000/2718)^165) <
      (97/10:ℝ)*(10:ℝ)^(-69:ℤ) := by norm_num
  have f2 : 2*((330:ℝ)*(1000/2718)^330) < (3/10:ℝ)*(10:ℝ)^(-69:ℤ) := by
    have hp : (1000/2718:ℝ)^330 ≤ (1/2:ℝ)^330 :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 330))
      (by norm_num : (0:ℝ) ≤ 2)).trans_lt (by
        rw [show (1/2:ℝ)^330 = ((1/2:ℝ)^165)^2 from by rw [← pow_mul]]
        norm_num)
  calc Eπ x ≤ _ := hraw
    _ ≤ (1/(8*3.14:ℝ))*((330:ℝ)^2*(1000/2718)^165) +
        2*((330:ℝ)*(1000/2718)^330) := by
      have ha := h1'.trans (mul_le_mul_of_nonneg_left h165 (sq_nonneg (330:ℝ)))
      have hb := h2'.trans (mul_le_mul_of_nonneg_left h330 (by norm_num : (0:ℝ)≤330))
      exact add_le_add (mul_le_mul hi ha (by positivity) (by norm_num))
        (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ < (97/10:ℝ)*(10:ℝ)^(-69:ℤ) + (3/10:ℝ)*(10:ℝ)^(-69:ℤ) := add_lt_add f1 f2
    _ = _ := by norm_num

#print axioms uniform_offset_error
end TableCompare
