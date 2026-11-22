import ActualFinite
import RHTailActual640
namespace RHContinuation.Ramanujan
open Real IEANTN Set RamanujanPV.AnalyticTransition Ramanujan640
open Ramanujan640.RHTail Ramanujan640.AnalyticBarrier
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"
theorem actual_tail_profile (hRH : SharedRH.hypothesis)
    (hButhe : Buthe2016.v1.theorem_2_li_minus_pi)
    {l : ℝ} (hl : 42 ≤ l) : baseBound l-D a l ≤ RamStudy.RG (exp l) := by
  have hl0 : 0 < l := by linarith
  have hl1 : 1 < l := by linarith
  have hlm : l-1 ≠ 0 := by linarith
  let B : ℝ := 1+14/l+145/l^2+1412/l^3-1/1000
  have hbase : B ≤ l^4*(l/(l-1)*RamStudy.w (l-1)-(RamStudy.w l)^2) := by
    simpa only [B,baseBound] using actual_base_no_series (by linarith : (27:ℝ)≤l)
  have hw : RamStudy.w l ≤ 21/20 := by
    have h := actual_w_tail_no_series hl
    simpa only [w_actual_eq] using h
  have hc := actual_count_RH_bounds hRH hButhe (l:=l) (by linarith)
  have hd := actual_count_RH_bounds hRH hButhe (l:=l-1) (by linarith)
  have hs := RamStudy.signed_consumer hl1 hbase
    (show RamStudy.count l ≤ RamStudy.w l-(-eta l) by linarith [hc.2]) hd.1
  have hsign : B-l^4*(l/(l-1)*eta (l-1))-
      l^4*(2*RamStudy.w l*eta l)-l^4*(eta l)^2 ≤ RamStudy.RG (exp l) := by
    convert! hs using 1 <;> ring
  have hshift : l^4*(l/(l-1)*eta (l-1)) =
      a*l^5*(l-1)*exp ((1-l)/2) := by
    unfold eta
    rw [show -(l-1)/2=(1-l)/2 by ring]
    field_simp [hlm]
    <;> ring
  have hetanonneg : 0 ≤ eta l := by unfold eta;exact mul_nonneg (mul_nonneg a_bounds.1 (sq_nonneg _)) (exp_pos _).le
  have hcross : l^4*(2*RamStudy.w l*eta l) ≤
      (21/10:ℝ)*a*l^6*exp (-l/2) := by
    have h := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2*l^4*eta l by positivity)
    dsimp [eta] at h ⊢
    nlinarith
  have hsquare : l^4*(eta l)^2 = a^2*l^8*exp (-l) := by
    have he : exp (-l/2)^2=exp (-l) := by
      rw [← exp_nat_mul]
      congr 1
      ring
    unfold eta
    rw [mul_pow,mul_pow,he]
    ring
  rw [hshift,hsquare] at hsign
  dsimp [B] at hsign
  unfold baseBound D
  linarith


lemma actual_baseBound_antitone {l u : ℝ} (hl : 0 < l) (hu : l ≤ u) :
    baseBound u ≤ baseBound l := by
  have h1 := invpow_antitone hl hu 1
  have h2 := invpow_antitone hl hu 2
  have h3 := invpow_antitone hl hu 3
  unfold baseBound
  norm_num only [pow_one] at h1
  simp only [div_eq_mul_inv] at *
  linarith

lemma actual_tail_42_43_scalar : (4/5:ℝ) ≤ baseBound 43-D (25/628:ℝ) 42 := by
  unfold baseBound D
  interval_decide 80 (trust := kernel)
lemma actual_tail_43_46_scalar : (4/5:ℝ) ≤ baseBound 46-D (25/628:ℝ) 43 := by
  unfold baseBound D
  interval_decide 80 (trust := kernel)
lemma actual_tail_46_scalar : (4/5:ℝ) ≤ (999/1000:ℝ)-D (25/628:ℝ) 46 := by
  unfold D
  interval_decide 80 (trust := kernel)

/-- Retaining the full base profile and monotone loss proves a 0.8 whole-ray
margin, rather than separately throwing away all positive lower-order terms. -/
theorem actual_tail_four_fifths (hRH : SharedRH.hypothesis)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {l : ℝ} (hl : 42 ≤ l) : (4/5:ℝ) ≤ RamStudy.RG (exp l) := by
  have hmain := actual_tail_profile hRH hS hl
  have hDc := D_mono_c a_bounds.1 a_bounds.2 (by linarith : (1:ℝ) ≤ l)
  by_cases h43 : l ≤ 43
  · have hB := actual_baseBound_antitone (by linarith : (0:ℝ)<l) h43
    have hD := D_antitone (by norm_num : (0:ℝ) ≤ 25/628)
      (show (42:ℝ) ∈ Ici 42 by simp) hl hl
    linarith [actual_tail_42_43_scalar]
  by_cases h46 : l ≤ 46
  · have hB := actual_baseBound_antitone (by linarith : (0:ℝ)<l) h46
    have hD := D_antitone (by norm_num : (0:ℝ) ≤ 25/628)
      (show (43:ℝ) ∈ Ici 42 by norm_num) hl (by linarith : (43:ℝ) ≤ l)
    linarith [actual_tail_43_46_scalar]
  · have hB : (999/1000:ℝ) ≤ baseBound l := by
      have h1 : (0:ℝ) ≤ 14/l := by positivity
      have h2 : (0:ℝ) ≤ 145/l^2 := by positivity
      have h3 : (0:ℝ) ≤ 1412/l^3 := by positivity
      unfold baseBound
      linarith
    have hD := D_antitone (by norm_num : (0:ℝ) ≤ 25/628)
      (show (46:ℝ) ∈ Ici 42 by norm_num) hl (by linarith : (46:ℝ) ≤ l)
    linarith [actual_tail_46_scalar]

#print axioms actual_tail_profile
#print axioms actual_tail_four_fifths
end RHContinuation.Ramanujan
