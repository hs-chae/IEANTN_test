import SynergyAnalytic.HeightPointSourceIdentity
namespace SynergyAnalytic.HeightPoint
open Real WinnerOriginalScalars WinnerBetaA.HeightSource WinnerNewHeightSource
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

 theorem stripProduct_exp_repr {UL VR d delta t:ℝ}
    (hUL:0<UL) (hVR:0<VR) (ht:0<t) (hd:0<delta) :
    stripProduct UL VR (7/8) (1+delta/t) (d/t) =
      Real.exp (((1/8+(d+delta)/t)/(1/2+delta/t))*Real.log UL+
        (1-(1/8+(d+delta)/t)/(1/2+delta/t))*Real.log VR) := by
  have hw : (1/2:ℝ)+delta/t ≠ 0 := by have hp:=div_pos hd ht;linarith
  unfold stripProduct
  rw [Real.rpow_def_of_pos hUL,Real.rpow_def_of_pos hVR,←Real.exp_add]
  congr 1
  have he : (1+delta/t)-(1/2:ℝ)=1/2+delta/t := by ring
  rw [he]
  field_simp [hw,ht.ne']
  <;> ring

theorem point_theta_exact (t:ℝ) : r172 t=(1/8+((3681/10000:ℝ)+(3599/10000))/t)/(1/2+(3599/10000:ℝ)/t) := by
  norm_num [r172,r170,r169,r168,r167,r171,r30,r77,r64,r58,r3,r4,r55,div_eq_mul_inv]
  <;> first | trivial | ring

theorem point_prefactor_exact (t:ℝ) :
    r182 t=sourceSmoothingR*Real.exp (2*WinnerNewHeightSource.alpha)*t/(2*Real.pi*(3681/10000:ℝ)) := by
  norm_num [r182,r181,r180,r179,r178,r177,r35,r34,r33,r32,r31,r30,r29,r28,r36,r26,r2,r1,r5,r3,r58,r0,
    sourceSmoothingR,WinnerOriginalScalars.height,WinnerNewHeightSource.alpha,pow_two,div_eq_mul_inv]
  <;> first | trivial | ring

theorem point_main_repr (t:ℝ) : r184 t=r182 t*Real.exp
    (r172 t*Real.log (continuousLeftCap (373/200) (1273/2000) (129/250) (Real.exp t))+
    (1-r172 t)*Real.log (continuousRightCap (3599/10000) (Real.exp t))) := by
  simp only [r184,r183,r176,r173,r175,r174,r165,r166,r0,div_one,
    point_left_exact,point_right_exact,sub_eq_add_neg]

theorem point_main_exact {t:ℝ} (ht:0<t) : r184 t=
    continuousMain (3681/10000) (3599/10000) (373/200) (1273/2000) (129/250) (7/8) (Real.exp t) := by
  have hT:1<Real.exp t:=Real.one_lt_exp_iff.mpr ht
  have hL:=continuousLeftCap_pos (j0:=(373/200:ℝ)) (j1:=(1273/2000:ℝ)) (j2:=(129/250:ℝ))
    (by norm_num) (by norm_num) (by norm_num) hT
  have hR:=continuousRightCap_pos (delta:=(3599/10000:ℝ)) (by norm_num) hT
  rw [point_main_repr,point_prefactor_exact,point_theta_exact]
  unfold continuousMain
  rw [Real.log_exp]
  simp only [rightLine,Real.log_exp]
  rw [stripProduct_exp_repr hL hR ht (by norm_num)]

theorem point_slope_exact (t:ℝ) : r186 t=
    continuousSlope (3599/10000) (373/200) (1273/2000) (129/250) (Real.exp t) := by
  simp only [r186,r185,r165,r166,r171,r167,r30,r77,r4,r64,r58,point_left_exact,point_right_exact,
    continuousSlope,rightLine,Real.log_exp]
  congr 1
  ring

#print axioms point_main_exact
#print axioms point_slope_exact
end SynergyAnalytic.HeightPoint
