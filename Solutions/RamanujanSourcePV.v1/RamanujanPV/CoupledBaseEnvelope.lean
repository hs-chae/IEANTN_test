/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.AnalyticTransition
import RamanujanPV.CoupledUniformBounds

/-! Monotonicity and exact Taylor endpoint for the 1.25T coupled strip.
The li series and derivative identities remain the original explicit inputs.
The Axler li lower bound is needed over this expanded strip and is displayed
as such; the former [1.49T,1e19] type is not silently reused outside its range. -/
namespace RamanujanPV.CoupledBaseEnvelope
open Real Set RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable def R (li : ℝ → ℝ) (x : ℝ) : ℝ :=
  li (x/Real.exp 1)-(389/200:ℝ)*Real.sqrt (x/Real.exp 1)/(Real.log x-1)-
    (li x)^2*Real.log x/(Real.exp 1*x)
noncomputable def Rderiv (li : ℝ → ℝ) (x : ℝ) : ℝ :=
  (li x*(Real.log x-1)-x)^2/(Real.exp 1*x^2*(Real.log x-1))-
    (389/400:ℝ)*(Real.log x-3)/(Real.exp 1*(Real.log x-1)^2*Real.sqrt (x/Real.exp 1))

lemma R_hasDerivAt {li : ℝ → ℝ} (hderiv : LogIntegralDerivative li)
    {x : ℝ} (hx : 6 < x) (hL : 1 < Real.log x) :
    HasDerivAt (R li) (Rderiv li x) x := by
  have hx0 : 0 < x := by linarith
  have hE := Real.exp_pos 1
  have hxe : 2 < x/Real.exp 1 := by
    apply (lt_div_iff₀ hE).mpr
    linarith [Real.exp_one_lt_d9]
  have hln : Real.log x ≠ 0 := by linarith
  have hm : Real.log x-1 ≠ 0 := by linarith
  have hroot : 0 < Real.sqrt (x/Real.exp 1) := Real.sqrt_pos.mpr (by positivity)
  have hlogxe : Real.log (x/Real.exp 1) = Real.log x-1 := by
    rw [Real.log_div hx0.ne' hE.ne',Real.log_exp]
  have hs := ((hasDerivAt_id x).div_const (Real.exp 1)).sqrt (show x/Real.exp 1 ≠ 0 by positivity)
  have ha := (hderiv (x/Real.exp 1) hxe).comp x ((hasDerivAt_id x).div_const (Real.exp 1))
  have ht := ((hs.const_mul (389/200:ℝ)).div ((Real.hasDerivAt_log hx0.ne').sub_const 1) hm)
  have hu := (((hderiv x (by linarith)).pow 2).mul (Real.hasDerivAt_log hx0.ne')).div
    ((hasDerivAt_id x).const_mul (Real.exp 1)) (by positivity)
  have hd := (ha.sub ht).sub hu
  have hsq : Real.exp 1*(Real.sqrt (x/Real.exp 1))^2 = x := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  convert! hd using 1
  dsimp [Rderiv]
  rw [hlogxe]
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
  generalize hAv : li x = A
  generalize hLv : Real.log x = L
  generalize hSv : Real.sqrt (x/Real.exp 1) = s
  rw [hSv] at hsq hroot
  rw [hLv] at hL
  rw [← hsq]
  field_simp [show L ≠ 0 by linarith,show L-1 ≠ 0 by linarith]
  <;> ring

theorem strip_height {x : ℝ} (hx : x ∈ Icc (1250000000000:ℝ) 1490000000000) :
    (1061/1000:ℝ)*(Real.log x)^4 ≤ Real.sqrt (x/Real.exp 1) := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hL := CoupledUniformBounds.log_lower hx.1
  have hLhi : Real.log x ≤ (281/10:ℝ) := by
    have h := Real.log_le_log hx0 hx.2
    linarith [log_endpoint_bounds.2]
  have hroot : (677000:ℝ) ≤ Real.sqrt (x/Real.exp 1) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (Real.exp_pos 1)).2
    have h := mul_le_mul_of_nonneg_left CoupledUniformBounds.exp_one_upper
      (sq_nonneg (677000:ℝ))
    nlinarith [hx.1]
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log x) hLhi 4
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤1061/1000)
  have hn : (1061/1000:ℝ)*(281/10)^4 ≤ 677000 := by norm_num
  exact (hm.trans hn).trans hroot

theorem derivative_nonneg {li : ℝ → ℝ}
    (hAxler : ∀ x ∈ Icc (1250000000000:ℝ) 1490000000000,
      x/(Real.log x-1-1/Real.log x) < li x)
    {x : ℝ} (hx : x ∈ Icc (1250000000000:ℝ) 1490000000000) :
    0 ≤ Rderiv li x := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hL := CoupledUniformBounds.log_lower hx.1
  have hs : 0 < Real.sqrt (x/Real.exp 1) := Real.sqrt_pos.2 (by positivity)
  have hold := base_derivative_nonneg hx0 (Real.exp_pos 1)
    (by linarith : 4 ≤ Real.log x) hs (hAxler x hx) (strip_height hx)
  have hratio : 0 ≤ (Real.log x-3) /
      (Real.exp 1*(Real.log x-1)^2*Real.sqrt (x/Real.exp 1)) := by
    exact div_nonneg (by linarith) (by positivity)
  have hcoef := mul_le_mul_of_nonneg_right
    (by norm_num : (389/400:ℝ)≤1061/1000) hratio
  unfold Rderiv
  rw [mul_div_assoc] at hold ⊢
  linarith

theorem monotone_strip {li : ℝ → ℝ} (hderiv : LogIntegralDerivative li)
    (hAxler : ∀ x ∈ Icc (1250000000000:ℝ) 1490000000000,
      x/(Real.log x-1-1/Real.log x) < li x) :
    MonotoneOn (R li) (Icc (1250000000000:ℝ) 1490000000000) := by
  have hd : ∀ x ∈ Icc (1250000000000:ℝ) 1490000000000,
      HasDerivAt (R li) (Rderiv li x) x := by
    intro x hx
    exact R_hasDerivAt hderiv (by linarith [hx.1])
      (by linarith [CoupledUniformBounds.log_lower hx.1])
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact derivative_nonneg hAxler (interior_subset hx)

#print axioms R_hasDerivAt
#print axioms strip_height
#print axioms derivative_nonneg
#print axioms monotone_strip

lemma log_mantissa1250 :
    (1282774448449455/10000000000000000:ℝ) ≤
      Real.log ((1+(146961301/2294444949:ℝ))/(1-(146961301/2294444949:ℝ))) ∧
    Real.log ((1+(146961301/2294444949:ℝ))/(1-(146961301/2294444949:ℝ))) ≤
      1282774448449456/10000000000000000 := by
  have h := log_atanh80_bounds (r:=(146961301/2294444949:ℝ))
    (lo:=(1282774448449455/10000000000000000:ℝ))
    (hi:=(12827744484494559/100000000000000000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [logAtanhPoly,Finset.sum_range_succ])
    (by norm_num [logAtanhPoly,Finset.sum_range_succ])
  exact ⟨h.1,h.2.trans (by norm_num)⟩

lemma log1250_bounds :
    (278541646672427/10000000000000:ℝ) ≤ Real.log 1250000000000 ∧
    Real.log 1250000000000 ≤ 278541646672428/10000000000000 := by
  let m : ℝ := (1+(146961301/2294444949:ℝ))/(1-(146961301/2294444949:ℝ))
  have hm : (0:ℝ) < m := by dsimp [m]; norm_num
  have hid : Real.log (1250000000000:ℝ) = 40*Real.log 2+Real.log m := by
    calc
      _ = Real.log ((2:ℝ)^40*m) := by congr 1; dsimp [m]; norm_num
      _ = Real.log ((2:ℝ)^40)+Real.log m := Real.log_mul (by positivity) hm.ne'
      _ = 40*Real.log 2+Real.log m := by rw [Real.log_pow]; norm_num
  have h2 := log_two_decimal
  have h3 := log_mantissa1250
  change _ ≤ Real.log m ∧ Real.log m ≤ _ at h3
  rw [hid]
  constructor <;> linarith

lemma series1250_lower :
    (46618066581:ℝ) ≤ eiPartial (278541646672427/10000000000000:ℝ) := by
  norm_num [eiPartial,eiTerm,Finset.sum_range_succ,Nat.factorial]
lemma series1250_upper :
    eiPartial (278541646672428/10000000000000:ℝ)+
      (4/3:ℝ)*eiTerm (278541646672428/10000000000000:ℝ) 200 ≤ 46618066582 := by
  norm_num [eiPartial,eiTerm,Finset.sum_range_succ,Nat.factorial]
lemma series1250e_lower :
    (17815390993:ℝ) ≤ eiPartial (268541646672427/10000000000000:ℝ) := by
  norm_num [eiPartial,eiTerm,Finset.sum_range_succ,Nat.factorial]
lemma series1250e_upper :
    eiPartial (268541646672428/10000000000000:ℝ)+
      (4/3:ℝ)*eiTerm (268541646672428/10000000000000:ℝ) 200 ≤ 17815390994 := by
  norm_num [eiPartial,eiTerm,Finset.sum_range_succ,Nat.factorial]

lemma log_log26_29 {z : ℝ} (hz26 : 26 ≤ z) (hz29 : z ≤ 29) :
    3 ≤ Real.log z ∧ Real.log z ≤ 4 := by
  have hz : 0 < z := by linarith
  have h3 : Real.exp (3:ℝ) ≤ 26 := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le CoupledUniformBounds.exp_one_upper 3
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    exact h.trans (by norm_num)
  have h4 : 29 ≤ Real.exp (4:ℝ) := by
    have he : (5/2:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5/2) he 4
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    exact (show (29:ℝ) ≤ 625/16 by norm_num).trans h
  exact ⟨(Real.le_log_iff_exp_le hz).2 (h3.trans hz26),
    (Real.log_le_iff_le_exp hz).2 (hz29.trans h4)⟩

lemma li1250_bounds {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li) :
    (46618066584:ℝ) ≤ li 1250000000000 ∧ li 1250000000000 ≤ 46618066587 := by
  have hL := log1250_bounds
  have hlog := log_log26_29 (by linarith [hL.1] : 26≤Real.log 1250000000000)
    (by linarith [hL.2] : Real.log 1250000000000≤29)
  have h := li_from_series hseries (x:=1250000000000)
    (a:=(278541646672427/10000000000000:ℝ))
    (b:=(278541646672428/10000000000000:ℝ))
    (by norm_num) (by norm_num) hL.1 hL.2 (by norm_num)
    hlog.1 hlog.2 series1250_lower series1250_upper
  constructor <;> linarith

lemma li1250e_bounds {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li) :
    (17815390996:ℝ) ≤ li (1250000000000/Real.exp 1) ∧
    li (1250000000000/Real.exp 1) ≤ 17815390999 := by
  have hL := log1250_bounds
  have hid : Real.log (1250000000000/Real.exp 1) = Real.log 1250000000000-1 := by
    rw [Real.log_div (by norm_num) (Real.exp_ne_zero 1),Real.log_exp]
  have hlog := log_log26_29 (by linarith [hL.1] : 26≤Real.log 1250000000000-1)
    (by linarith [hL.2] : Real.log 1250000000000-1≤29)
  have hx : 1 < (1250000000000:ℝ)/Real.exp 1 := by
    apply (lt_div_iff₀ (Real.exp_pos 1)).2
    linarith [Real.exp_one_lt_d9]
  have h := li_from_series hseries (x:=1250000000000/Real.exp 1) (llo:=3) (lhi:=4)
    (a:=(268541646672427/10000000000000:ℝ))
    (b:=(268541646672428/10000000000000:ℝ))
    hx (by norm_num) (by rw [hid]; linarith [hL.1])
    (by rw [hid]; linarith [hL.2]) (by norm_num)
    (by simpa only [hid] using hlog.1) (by simpa only [hid] using hlog.2)
    series1250e_lower series1250e_upper
  constructor <;> linarith

lemma sqrt1250e_upper : Real.sqrt (1250000000000/Real.exp 1) ≤ (678122:ℝ) := by
  apply Real.sqrt_le_iff.2
  refine ⟨by norm_num, ?_⟩
  apply (div_le_iff₀ (Real.exp_pos 1)).2
  nlinarith [Real.exp_one_gt_d9]

theorem endpoint_positive {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li) :
    50 < R li 1250000000000 := by
  let Llo : ℝ := 278541646672427/10000000000000
  let Lhi : ℝ := 278541646672428/10000000000000
  have hL := log1250_bounds
  change Llo ≤ Real.log 1250000000000 ∧ Real.log 1250000000000 ≤ Lhi at hL
  have hli := li1250_bounds hseries
  have hlie := li1250e_bounds hseries
  have hroot := sqrt1250e_upper
  have hlogpos : 0 < Real.log (1250000000000:ℝ) := Real.log_pos (by norm_num)
  have hUpos : 0 ≤ li 1250000000000 := by linarith [hli.1]
  have hUsq := pow_le_pow_left₀ hUpos hli.2 2
  have hT : (389/200:ℝ)*Real.sqrt (1250000000000/Real.exp 1)/(Real.log 1250000000000-1) ≤
      (389/200:ℝ)*678122/(Llo-1) := by
    apply div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left hroot (by norm_num)) (by dsimp [Llo]; norm_num)
    linarith [hL.1]
  have hE : (27182818283/10000000000:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hW : (li 1250000000000)^2*Real.log 1250000000000/(Real.exp 1*1250000000000) ≤
      (46618066587:ℝ)^2*Lhi/((27182818283/10000000000:ℝ)*1250000000000) := by
    apply div_le_div₀ (by positivity)
      (mul_le_mul hUsq hL.2 hlogpos.le (by norm_num)) (by norm_num)
    nlinarith [hE]
  have hnum : 50 < (17815390996:ℝ)-(389/200:ℝ)*678122/(Llo-1)-
      (46618066587:ℝ)^2*Lhi/((27182818283/10000000000:ℝ)*1250000000000) := by
    dsimp [Llo,Lhi]
    norm_num
  unfold R
  linarith [hlie.1]

theorem strip_positive {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li)
    (hderiv : LogIntegralDerivative li)
    (hAxler : ∀ x ∈ Icc (1250000000000:ℝ) 1490000000000,
      x/(Real.log x-1-1/Real.log x) < li x)
    {x : ℝ} (hx : x ∈ Icc (1250000000000:ℝ) 1490000000000) :
    50 < R li x := by
  exact (endpoint_positive hseries).trans_le
    (monotone_strip hderiv hAxler (by constructor <;> norm_num) hx hx.1)

#print axioms log1250_bounds
#print axioms series1250_lower
#print axioms series1250_upper
#print axioms series1250e_lower
#print axioms series1250e_upper
#print axioms li1250_bounds
#print axioms li1250e_bounds
#print axioms endpoint_positive
#print axioms strip_positive
end RamanujanPV.CoupledBaseEnvelope
