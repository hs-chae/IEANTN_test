import Ram620Result
import IEANTN.Nodes.RHPrimeCounting.v1.Conclusions
import IEANTN.Nodes.RamanujanGap.v4.Conclusions
namespace RamanujanGap.v4
open Real IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0

theorem challenge_margin_620b (rh : RH.v1.hypothesis) (hg : RHPrimeCounting.v1.gm_source)
    (hp : Buthe.v1.theorem_2_psi) (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (h1 : Buthe.v1.table_1_interval_bounds) (h2 : Buthe.v1.table_2_interval_bounds)
    (hl : Buthe.v1.theorem_2_li_minus_pi) (hu : Buthe.v1.theorem_2_li_gt_pi)
    (hs : Buthe2016.v1.theorem_2_li_minus_pi) : margin_620b := by
  intro x hx
  have h := RHLimit.Ram620.actual_ramanujan_620b rh hg hp hj h1 h2 hl hu hs hx
  have hx0 : 0 < x := by linarith
  have hlog : 0 < log x := log_pos (by linarith : 1 < x)
  have hpos : 0 < log x^6/x^2 := by positivity
  have he : (log x^6/x^2)*((1/1000:ℝ)*x^2/(log x)^6) = 1/1000 := by
    field_simp [hx0.ne',hlog.ne']
  apply (mul_le_mul_iff_right₀ hpos).mp
  rw [he]
  exact h

/-- Retain the ENTIRE old v3 profile, including the polynomial and144/L² tail. -/
theorem challenge_full_profile (hnew : margin_620b)
    (hold : RamanujanGap.v3.full_profile) : full_profile := by
  intro x hx
  unfold profile
  split_ifs with h640
  · exact hold x h640
  · exact hnew x hx

theorem challenge_ramanujan (h : margin_620b) : ramanujan := by
  intro x hx
  have hb := h x hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith : 1 < x)
  have hp : 0 < (1/1000:ℝ)*x^2/(log x)^6 := by positivity
  unfold RamanujanGap.v1.gap at hb
  linarith

theorem challenge_retains_original_margin : retains_original_margin := by
  intro x hx
  simp only [profile,if_pos hx]
#print axioms challenge_margin_620b
#print axioms challenge_full_profile
#print axioms challenge_ramanujan
#print axioms challenge_retains_original_margin
end RamanujanGap.v4
