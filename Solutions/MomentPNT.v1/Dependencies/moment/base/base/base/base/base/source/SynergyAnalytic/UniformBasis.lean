import SynergyAnalytic.ContinuousProfile
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerOriginalScalars WinnerBetaA.ActualObject
open WinnerBetaA.HeightSource WinnerNewHeightSource
set_option maxHeartbeats 0

noncomputable def uniformBasisBudget (A M1 M2 hbar r eps eta j0 j1 j2 : ℝ) : ℝ :=
  2*Real.exp ((601/5000:ℝ)/(2*A^2))*
    ((1+eps)*(611/1000:ℝ)^2*((1+eta)*(M1*(j0+(2/hbar)*j1+(1/hbar^2)*j2)+M2*universalPeak)+
      (1+1/eta)*r^2*(M1*gaussianArea+M2))+
      (1+1/eps)*gaussianArea/(A^((1:ℝ)/3)*Real.log A^3))

/-- The same three universal integrals also give an all-future-height coarse
profile. This supplies the far tail independently of the old four65536-cell
Gaussian certificates. Every scalar allowance is an explicit residual. -/
theorem actual_left_uniform_basis {d delta A T M1 M2 hbar r eps eta j0 j1 j2 U : ℝ}
    (h : PrimaryInputs d delta) (hcaps : UniversalBasisCaps j0 j1 j2)
    (hA : height≤A) (hAT : A≤T) (hhbar : 14≤hbar) (hhA : hbar≤Real.log A)
    (he : 0<eps) (heta : 0<eta)
    (hM1 : meanOne A≤M1) (hM2 : meanTwo A≤M2)
    (hr : (1461/1000:ℝ)/zetaScale A≤r)
    (h0 : 0≤j0) (h1 : 0≤j1) (h2 : 0≤j2)
    (hU : uniformBasisBudget A M1 M2 hbar r eps eta j0 j1 j2≤U) :
    sourceMoment T (1/2)≤U*T^((4:ℝ)/3)*Real.log T^3 := by
  have hA1 : 1<A := lt_of_lt_of_le (by norm_num [height]) hA
  have hT1 : 1<T := hA1.trans_le hAT
  have hAp : 0<A := by linarith
  have hTp : 0<T := by linarith
  have hlA : 0<Real.log A := Real.log_pos hA1
  have hlT : 0<Real.log T := Real.log_pos hT1
  have hlAT := Real.log_le_log hAp hAT
  have hm1 := (meanOne_nonneg hA1).trans hM1
  have hm2 := (meanTwo_nonneg hA1).trans hM2
  have hMT1 := (meanOne_mono hA1 hAT).trans hM1
  have hMT2 := (meanTwo_mono hA1 hAT).trans hM2
  have hzA : 0<zetaScale A := by unfold zetaScale;positivity
  have hzAT : zetaScale A≤zetaScale T := by unfold zetaScale;gcongr
  have hrT : (1461/1000:ℝ)/zetaScale T≤r :=
    (div_le_div_of_nonneg_left (by norm_num) hzA hzAT).trans hr
  have hmean : ∀t>0,(∫u in (0:ℝ)..t,‖mollifier T (vertical (1/2) u)‖^2)≤
      (M1*t+M2*T)*Real.log T := by
    intro t ht
    exact (h.mollifierMeanSquare T (hA.trans hAT) t ht).trans
      (mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_right hMT1 ht.le) (mul_le_mul_of_nonneg_right hMT2 hTp.le)) hlT.le)
  have hs := actual_source_moment_from_basis hT1 hhbar (hhA.trans hlAT) hrT he heta hm1 hm2
    hcaps h.lowZeta h.reversZeta hmean (h.sourceSmoothing T (hA.trans hAT))
  let C := (1+eta)*(M1*(j0+(2/hbar)*j1+(1/hbar^2)*j2)+M2*universalPeak)+
    (1+1/eta)*r^2*(M1*gaussianArea+M2)
  have hg : 0<gaussianArea := by unfold gaussianArea;positivity
  have hp : 0<universalPeak := Real.exp_pos _
  have hh : 0<hbar := by linarith
  have hC : 0≤C := by dsimp [C];positivity
  have heq : (zetaScale T)^2*(T*Real.log T) =
      (611/1000:ℝ)^2*T^((4:ℝ)/3)*Real.log T^3 := by
    have hpT : (T^((1:ℝ)/6))^2=T^((1:ℝ)/3) := by
      rw [←Real.rpow_mul_natCast hTp.le];norm_num
    have h4 : T^((4:ℝ)/3)=T*T^((1:ℝ)/3) := by
      rw [show (4:ℝ)/3=1+1/3 by ring,Real.rpow_add hTp,Real.rpow_one]
    unfold zetaScale
    rw [mul_pow,mul_pow,hpT,h4]
    ring
  have hnorm : errorBudget T hbar r eps eta M1 M2 j0 j1 j2 =
      ((1+eps)*(611/1000:ℝ)^2*C+
        (1+1/eps)*gaussianArea/(T^((1:ℝ)/3)*Real.log T^3))*T^((4:ℝ)/3)*Real.log T^3 := by
    unfold errorBudget
    change (1+eps)*(zetaScale T)^2*(T*Real.log T)*C+(1+1/eps)*T*gaussianArea = _
    rw [mul_assoc (1+eps) ((zetaScale T)^2) (T*Real.log T),heq]
    have h4 : T^((4:ℝ)/3)=T*T^((1:ℝ)/3) := by
      rw [show (4:ℝ)/3=1+1/3 by ring,Real.rpow_add hTp,Real.rpow_one]
    rw [h4]
    field_simp
    <;> ring
  have hscale : 0≤T^((4:ℝ)/3)*Real.log T^3 := by positivity
  have homega : Real.exp ((601/5000:ℝ)/(2*T^2))≤Real.exp ((601/5000:ℝ)/(2*A^2)) := by
    apply Real.exp_le_exp.mpr
    gcongr
  have hfrac : (1+1/eps)*gaussianArea/(T^((1:ℝ)/3)*Real.log T^3)≤
      (1+1/eps)*gaussianArea/(A^((1:ℝ)/3)*Real.log A^3) := by
    gcongr
  have hnormCap : 2*Real.exp ((601/5000:ℝ)/(2*T^2))*
      ((1+eps)*(611/1000:ℝ)^2*C+(1+1/eps)*gaussianArea/(T^((1:ℝ)/3)*Real.log T^3))≤U := by
    apply LE.le.trans _ hU
    unfold uniformBasisBudget
    dsimp [C]
    exact mul_le_mul (mul_le_mul_of_nonneg_left homega (by norm_num))
      (add_le_add le_rfl hfrac) (by positivity) (by positivity)
  rw [hnorm] at hs
  have hhcap := mul_le_mul_of_nonneg_right hnormCap hscale
  nlinarith

#print axioms actual_left_uniform_basis
end SynergyAnalytic
