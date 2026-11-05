/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectPrimePower
namespace WinnerDirectKernel
open Real Set MeasureTheory
set_option maxHeartbeats 0

 theorem direct_height_domains {L u : ℝ} (hL : 300≤L) (hu : u∈Icc ((3/4)*L) L) :
    40≤u ∧ max 51 u<exp (L/3) ∧ exp (L/3)<(exp (u/2)-2)/2 := by
  have hLp : 0<L := by linarith
  have he1:=add_one_le_exp (L/6)
  have he2 : (1+L/6)^2≤exp (L/6)^2 := by
    simpa only [add_comm] using pow_le_pow_left₀ (by linarith : 0≤L/6+1) he1 2
  have hExp : exp (L/6)^2=exp (L/3) := by rw [pow_two,←exp_add];congr 1;ring
  rw [hExp] at he2
  have hT : L<exp (L/3) := by nlinarith
  have hd : L/3+2≤u/2 := by linarith [hu.1]
  have he : exp (L/3+2)≤exp (u/2) := exp_le_exp.mpr hd
  rw [exp_add] at he
  have he3 : (3:ℝ)≤exp 2 := by linarith [add_one_le_exp (2:ℝ)]
  have hm:=mul_le_mul_of_nonneg_left he3 (exp_pos (L/3)).le
  refine ⟨by linarith [hu.1],max_lt (by linarith) (hu.2.trans_lt hT),?_⟩
  linarith

 theorem direct_factor_bound {L : ℝ} (hL : 300≤L) :
    highFactor (1/8) 14 ((3/4)*L) L≤1001/1000 := by
  have hLp : 0<L := by linarith
  have hvp : 0<(3/4:ℝ)*L := by positivity
  have he : exp (-(1/8:ℝ)*(L-(3/4)*L))≤1 := exp_le_one_iff.mpr (by linarith)
  have h1 : 1/((14:ℝ)*L)≤1/(14*300) := by gcongr
  have hfrac2 : L/((14:ℝ)*((3/4)*L)^2)=8/(63*L) := by field_simp;ring
  have hfrac3 : 2*L/((14:ℝ)*(1/8)*((3/4)*L)^3)=512/(189*L^2) := by field_simp;ring
  have h2 : exp (-(1/8:ℝ)*(L-(3/4)*L))*L/(14*((3/4)*L)^2)≤8/(63*300) := by
    calc _ ≤L/(14*((3/4)*L)^2) := by
           apply div_le_div_of_nonneg_right _ (by positivity)
           simpa using mul_le_mul_of_nonneg_right he hLp.le
         _ =8/(63*L) := hfrac2
         _ ≤_ := by gcongr
  have h3 : 2*L/((14:ℝ)*(1/8)*((3/4)*L)^3)≤512/(189*(300:ℝ)^2) := by
    rw [hfrac3]
    gcongr
  unfold highFactor
  norm_num at h1 h2 h3 ⊢
  linarith

 theorem direct_remainders_tiny {L : ℝ} (hL : 300≤L) :
    ((13/2:ℝ)*L/exp (L/3)*(1+1/((3/4)*L))+4*L*exp (-(L/4))+
      (L^2+2*L)*exp (-L/2))*exp (L/8)≤1/100000000 := by
  have hLp : 0<L := by linarith
  have hv : 1≤(3/4:ℝ)*L := by linarith
  have hi : 1/((3/4:ℝ)*L)≤1 := (div_le_one (by positivity)).mpr hv
  have hlin := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 1
    (L0:=(300:ℝ)) (c:=1/8) (by norm_num) (by norm_num) hL
  have hlin2 := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 1
    (L0:=(300:ℝ)) (c:=1/5) (by norm_num) (by norm_num) hL
  have hquad := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 2
    (L0:=(300:ℝ)) (c:=1/4) (by norm_num) (by norm_num) hL
  have he37 : exp (-(300:ℝ)/8)≤1/(2:ℝ)^37 := by
    apply le_trans (exp_le_exp.mpr (by norm_num : -(300:ℝ)/8≤-(37:ℕ)))
    exact DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 37
  have he60:=DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 60
  have he75:=DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 75
  have hA : 4*L*exp (-(L/8))≤1200/(2:ℝ)^37 := by
    norm_num only [pow_one] at hlin
    have hExpL : -(L/8)=-(1/8:ℝ)*L := by ring
    have hlin' : L*exp (-(1/8:ℝ)*L)≤300*exp (-(300:ℝ)/8) := by
      convert! hlin using 1 <;> norm_num
    calc _ = 4*(L*exp (-(1/8:ℝ)*L)) := by rw [hExpL];ring
         _ ≤ 4*(300*exp (-(300:ℝ)/8)) := mul_le_mul_of_nonneg_left hlin' (by norm_num)
         _ ≤ 4*(300*(1/(2:ℝ)^37)) := by gcongr
         _ = _ := by ring
  have hT : (13/2:ℝ)*L*exp (-(5/24)*L)*(1+1/((3/4)*L))≤3900/(2:ℝ)^60 := by
    have hexp : exp (-(5/24)*L)≤exp (-(1/5)*L) := exp_le_exp.mpr (by linarith)
    have hh:=mul_le_mul_of_nonneg_left hexp hLp.le
    norm_num only [pow_one] at hlin2
    have he60' : exp (-(1/5:ℝ)*300)≤1/(2:ℝ)^60 := by convert he60 using 1 <;> norm_num
    have hm:=mul_le_mul_of_nonneg_left he60' (by norm_num : (0:ℝ)≤300)
    have hbound : L*exp (-(5/24)*L)≤300/(2:ℝ)^60 := by linarith
    have hh2:=mul_le_mul hbound (by linarith : 1+1/((3/4:ℝ)*L)≤2)
      (by positivity) (by positivity : 0≤300/(2:ℝ)^60)
    nlinarith
  have hP : (L^2+2*L)*exp (-(3/8)*L)≤181200/(2:ℝ)^75 := by
    have hx : L^2+2*L≤2*L^2 := by nlinarith
    have he : exp (-(3/8)*L)≤exp (-(1/4)*L) := exp_le_exp.mpr (by linarith)
    have hp:=mul_le_mul hx he (exp_pos _).le (by positivity : 0≤2*L^2)
    have he75' : exp (-(1/4:ℝ)*300)≤1/(2:ℝ)^75 := by convert he75 using 1 <;> norm_num
    have hm:=mul_le_mul_of_nonneg_left he75' (by norm_num : (0:ℝ)≤(300:ℝ)^2)
    nlinarith
  have heq :
      ((13/2:ℝ)*L/exp (L/3)*(1+1/((3/4)*L))+4*L*exp (-(L/4))+
        (L^2+2*L)*exp (-L/2))*exp (L/8)=
      (13/2)*L*exp (-(5/24)*L)*(1+1/((3/4)*L))+4*L*exp (-(L/8))+
        (L^2+2*L)*exp (-(3/8)*L) := by
    rw [div_eq_mul_inv,←exp_neg]
    simp only [add_mul]
    have h1 : exp (-(L/3))*exp (L/8)=exp (-(5/24)*L) := by rw [←exp_add];congr 1;ring
    have h2 : exp (-(L/4))*exp (L/8)=exp (-(L/8)) := by rw [←exp_add];congr 1;ring
    have h3 : exp (-L/2)*exp (L/8)=exp (-(3/8)*L) := by rw [←exp_add];congr 1;ring
    calc
      _ = (13/2:ℝ)*L*(exp (-(L/3))*exp (L/8))*(1+1/((3/4)*L))+
        4*L*(exp (-(L/4))*exp (L/8))+(L^2+2*L)*(exp (-L/2)*exp (L/8)) := by ring
      _ = _ := by rw [h1,h2,h3];ring
  rw [heq]
  norm_num at hA hT hP ⊢
  linarith

#print axioms direct_factor_bound
#print axioms direct_remainders_tiny
end WinnerDirectKernel
