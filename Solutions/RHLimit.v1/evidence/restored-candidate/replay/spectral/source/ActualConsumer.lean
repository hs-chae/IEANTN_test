import PrimePowerTransport
namespace Ramanujan640
open Real IEANTN
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem count_eq_deficit (l : ℝ) :
    RamStudy.count l = RamStudy.w l-deficit l*exp (-l/2) := by
  have he : exp l = exp (l/2)^2 := by
    rw [← exp_nat_mul]
    congr 1
    ring
  have hn : exp (-l/2) = (exp (l/2))⁻¹ := by
    rw [show -l/2 = -(l/2) by ring, exp_neg]
  unfold RamStudy.count RamStudy.w deficit
  rw [he, hn]
  field_simp
  <;> ring

theorem actual_count_upper {l c : ℝ} (h : c ≤ deficit l) :
    RamStudy.count l ≤ RamStudy.w l-c*exp (-l/2) := by
  rw [count_eq_deficit]
  have hh := mul_le_mul_of_nonneg_right h (exp_pos (-l/2)).le
  linarith

theorem actual_count_lower {l d : ℝ} (h : deficit l ≤ d) :
    RamStudy.w l-d*exp (-l/2) ≤ RamStudy.count l := by
  rw [count_eq_deficit]
  have hh := mul_le_mul_of_nonneg_right h (exp_pos (-l/2)).le
  linarith

/-- Actual right-continuous prime-count consumer. The three local analytic
inputs are separately discharged by source/series/slab lemmas; this is not
claimed as the completed global640b theorem. -/
theorem actual_signed_gap {l c d B : ℝ} (hl : 1 < l)
    (hB : B ≤ l^4*(l/(l-1)*RamStudy.w (l-1)-(RamStudy.w l)^2))
    (hc : c ≤ deficit l) (hd : deficit (l-1) ≤ d) :
    B-d*l^5/(l-1)*exp ((1-l)/2)+
      2*RamStudy.w l*c*l^4*exp (-l/2)-c^2*l^4*exp (-l) ≤
        RamStudy.RG (exp l) := by
  have h := RamStudy.signed_consumer hl hB
    (actual_count_upper hc) (actual_count_lower hd)
  have hs : exp (-(l-1)/2)=exp ((1-l)/2) := by congr 1;ring
  have hp : exp (-l/2)^2=exp (-l) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  convert h using 1
  rw [hs]
  rw [mul_pow, hp]
  ring

#print axioms count_eq_deficit
#print axioms actual_count_upper
#print axioms actual_count_lower
#print axioms actual_signed_gap
end Ramanujan640
