import RamanujanPV.Intervals
import SharedRH
import IEANTN.Nodes.RamanujanGap.v1.Conclusions
import IEANTN.Nodes.Buthe.v1.Conclusions

open Real IEANTN
namespace RamStudy

noncomputable def w (l : ℝ) := l / exp l * li (exp l)
noncomputable def count (l : ℝ) := l / exp l * primeCounting (exp l)
noncomputable def RG (x : ℝ) := log x ^ 6 / x ^ 2 * RamanujanGap.v1.gap x

theorem exact_scale {l : ℝ} (hl : 1 < l) :
    RG (exp l) = l^4 * (l / (l-1) * count (l-1) - count l ^ 2) := by
  simp only [RG, RamanujanGap.v1.gap, log_exp, count, exp_sub]
  field_simp [exp_ne_zero, show l ≠ 0 by linarith, show l-1 ≠ 0 by linarith]

theorem count_nonneg {l : ℝ} (hl : 0 ≤ l) : 0 ≤ count l := by
  unfold count primeCounting
  positivity

/-- Checked consumer for a signed two-endpoint envelope on the actual count. -/
theorem signed_consumer {l c d B : ℝ} (hl : 1 < l)
    (hB : B ≤ l^4 * (l / (l-1) * w (l-1) - w l ^ 2))
    (hc : count l ≤ w l - c)
    (hd : w (l-1) - d ≤ count (l-1)) :
    B - l^4 * (l / (l-1) * d) + l^4 * (2 * w l * c - c^2) ≤ RG (exp l) := by
  have hsq : (count l)^2 ≤ (w l - c)^2 :=
    pow_le_pow_left₀ (count_nonneg (by linarith)) hc _
  have hpos : 0 ≤ l/(l-1) := by positivity
  have hprod := mul_le_mul_of_nonneg_left hd hpos
  have hh : l/(l-1)*(w (l-1)-d)-(w l-c)^2 ≤
      l/(l-1)*count (l-1)-(count l)^2 := by linarith
  rw [exact_scale hl]
  calc
    _ ≤ l^4 * (l/(l-1)*(w (l-1)-d)-(w l-c)^2) := by
      calc
        _ ≤ l^4 * (l/(l-1)*w (l-1)-(w l)^2) - l^4 * (l/(l-1)*d) +
               l^4 * (2*w l*c-c^2) := by linarith
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

theorem buethe_deficit_on_row (ht : Buthe.v1.table_2_interval_bounds)
    {v a b x : ℝ} (hr : (v,a,b) ∈ Buthe.v1.table_2) (hx : v ≤ x) (hu : x ≤ 2*v) :
    a ≤ (li x - riemannPrimeCounting x) * log x / sqrt x ∧
    (li x - riemannPrimeCounting x) * log x / sqrt x ≤ b :=
  ht (v,a,b) hr x hx hu

#print axioms signed_consumer
#print axioms buethe_deficit_on_row
end RamStudy
