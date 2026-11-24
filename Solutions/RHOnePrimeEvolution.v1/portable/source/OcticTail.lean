import OcticFourier
import OcticBPTSpecialization
namespace RHOcticPush.Moments
open Real Set MeasureTheory Filter
set_option maxHeartbeats 0
lemma abs_eight (a b c d e f g h : ℝ) :
    |a+b+c+d+e+f+g+h| ≤ |a|+|b|+|c|+|d|+|e|+|f|+|g|+|h| := by
  calc
    _ ≤ |a+b+c+d+e+f+g|+|h| := abs_add_le _ _
    _ ≤ |a+b+c+d+e+f|+|g|+|h| := by linarith [abs_add_le (a+b+c+d+e+f) g]
    _ ≤ |a+b+c+d+e|+|f|+|g|+|h| := by linarith [abs_add_le (a+b+c+d+e) f]
    _ ≤ |a+b+c+d|+|e|+|f|+|g|+|h| := by linarith [abs_add_le (a+b+c+d) e]
    _ ≤ |a+b+c|+|d|+|e|+|f|+|g|+|h| := by linarith [abs_add_le (a+b+c) d]
    _ ≤ |a+b|+|c|+|d|+|e|+|f|+|g|+|h| := by linarith [abs_add_le (a+b) c]
    _ ≤ _ := by linarith [abs_add_le a b]
lemma abs_trig_term (c y v : ℝ) (k : ℕ) (hy : 0 < y) (hv : |v| ≤ 1) :
    |c*v/y^k| ≤ |c|/y^k := by
  rw [abs_div, abs_mul, abs_of_pos (pow_pos hy k)]
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg c) hv)
    (pow_nonneg hy.le k)
lemma transform_abs_poly {y : ℝ} (hy : 0 < y) :
    |EvenKernel.transform 4 y| ≤ 16/y^2+112/y^3+672/y^4+3360/y^5+
      13440/y^6+40320/y^7+80640/y^8+80640/y^9 := by
  rw [RHLimit.OcticFourier.transform_eq hy.ne']
  unfold RHLimit.OcticFourier.formula
  have h := abs_eight ((-16)*cos y/y^2) (112*sin y/y^3) (672*cos y/y^4)
    ((-3360)*sin y/y^5) ((-13440)*cos y/y^6) (40320*sin y/y^7)
    (80640*cos y/y^8) ((-80640)*sin y/y^9)
  have hc (c : ℝ) (k : ℕ) := abs_trig_term c y (cos y) k hy (abs_cos_le_one y)
  have hs (c : ℝ) (k : ℕ) := abs_trig_term c y (sin y) k hy (abs_sin_le_one y)
  have h0 := hc (-16) 2
  have h1 := hs 112 3
  have h2 := hc 672 4
  have h3 := hs (-3360) 5
  have h4 := hc (-13440) 6
  have h5 := hs 40320 7
  have h6 := hc 80640 8
  have h7 := hs (-80640) 9
  norm_num at h h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  linarith
lemma tail_term {c T y : ℝ} (hc : 0 ≤ c) (hT : 0 < T) (hy : T ≤ y) (k : ℕ) :
    c/y^(k+2) ≤ (c/T^k)/y^2 := by
  have hy0 : 0 < y := hT.trans_le hy
  have hp : T^k ≤ y^k := pow_le_pow_left₀ hT.le hy k
  have hd := div_le_div_of_nonneg_left hc (pow_pos hT k) hp
  have hh := div_le_div_of_nonneg_right hd (sq_nonneg y)
  simpa only [div_div, pow_add] using hh

theorem octic_tail_bound {y : ℝ} (hy : 1000 ≤ y) :
    |EvenKernel.transform 4 y| ≤ (16113/1000)/y^2 := by
  have hy0 : 0 < y := by linarith
  have hp := transform_abs_poly hy0
  have h (c : ℝ) (hc : 0 ≤ c) (k : ℕ) := tail_term hc
    (show (0 : ℝ) < 1000 by norm_num) hy k
  have ht := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add (h 16 (by norm_num) 0) (h 112 (by norm_num) 1))
      (h 672 (by norm_num) 2)) (h 3360 (by norm_num) 3))
      (h 13440 (by norm_num) 4)) (h 40320 (by norm_num) 5))
      (h 80640 (by norm_num) 6)) (h 80640 (by norm_num) 7)
  have hn : (16+112/(1000:ℝ)+672/1000^2+3360/1000^3+13440/1000^4+
      40320/1000^5+80640/1000^6+80640/1000^7) ≤ 16113/1000 := by norm_num
  have he : (16+112/(1000:ℝ)+672/1000^2+3360/1000^3+13440/1000^4+
      40320/1000^5+80640/1000^6+80640/1000^7)/y^2 =
      (16/1000^0)/y^2+(112/1000^1)/y^2+(672/1000^2)/y^2+(3360/1000^3)/y^2+
      (13440/1000^4)/y^2+(40320/1000^5)/y^2+(80640/1000^6)/y^2+
      (80640/1000^7)/y^2 := by ring
  apply hp.trans (ht.trans _)
  rw [← he]
  exact div_le_div_of_nonneg_right hn (sq_nonneg y)

lemma log_tail_integral {T : ℝ} (hT : 1 ≤ T) :
    (∫ y in Ioi T, log y/y^2) = (log T+1)/T := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t (ht : t ∈ Ici T) => BPTSpecialization.log_inverse_primitive_derivative
      (by linarith [ht.out]))
    (BPTSpecialization.log_sq_integrable hT)
    BPTSpecialization.log_inverse_primitive_limit
  rw [h]
  ring
#print axioms octic_tail_bound
#print axioms log_tail_integral
end RHOcticPush.Moments
