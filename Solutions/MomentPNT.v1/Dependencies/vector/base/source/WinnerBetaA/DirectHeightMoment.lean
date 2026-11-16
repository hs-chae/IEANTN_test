/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerBetaA.SignedHeight
namespace WinnerBetaA.DirectHeightMoment
open Real Set MeasureTheory
open WinnerBetaA.Minkowski
set_option maxHeartbeats 0

noncomputable def logF (F : ℝ→ℝ) (y : ℝ) : ℝ :=
  exp (2*y-(601/2500:ℝ)*exp (2*y))*F (exp y)

theorem source_gaussian {F K : ℝ→ℝ} {a1 T J : ℝ}
    (ha1 : 0<a1) (hT : 1<T) (hF : Continuous F)
    (hFpos : ∀x>0,0≤F x)
    (hDom : ∀y:ℝ,logF F y≤(a1^2*(log T^3*T^((4:ℝ)/3)))*K y)
    (hK : Integrable K) (hJ : (∫y,K y)≤J) :
    IntegrableOn (fun x => gaussianWeight x*F x) (Ioi 0) ∧
      (∫x in Ioi 0,gaussianWeight x*F x)≤(a1^2*(log T^3*T^((4:ℝ)/3)))*J := by
  have hTp : 0<T := by linarith
  have hl := log_pos hT
  let c : ℝ := a1^2*(log T^3*T^((4:ℝ)/3))
  have hc : 0≤c := by dsimp [c];positivity
  have hBig : Integrable (fun y => c*K y) := hK.const_mul c
  have hLog : Integrable (logF F) := by
    apply hBig.mono' (show AEStronglyMeasurable (logF F) volume by
      have hh : Continuous (logF F) := by unfold logF;fun_prop
      exact hh.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤logF F y by
        unfold logF;exact mul_nonneg (exp_pos _).le (hFpos _ (exp_pos y)))]
      exact hDom y
  have hcomp : (fun y:ℝ => exp y • (gaussianWeight (exp y)*F (exp y)))=logF F := by
    funext y
    have hp : (exp y)^2=exp (2*y) := by rw [←exp_nat_mul];norm_num
    have hw : exp y*gaussianWeight (exp y)=exp (2*y-(601/2500:ℝ)*exp (2*y)) := by
      unfold gaussianWeight
      calc
        _ = (exp y)^2*exp (-(601/2500:ℝ)*(exp y)^2) := by ring
        _ = exp (2*y)*exp (-(601/2500:ℝ)*exp (2*y)) := by rw [hp]
        _ = _ := by rw [←exp_add];congr 1;ring
    change exp y*(gaussianWeight (exp y)*F (exp y))=logF F y
    unfold logF
    rw [←mul_assoc,hw]
  have hG : IntegrableOn (fun x => gaussianWeight x*F x) (Ioi 0) := by
    apply (MeasureTheory.integrable_comp_exp _).mp
    rw [hcomp]
    exact hLog
  have hEq : (∫y,logF F y)=∫x in Ioi 0,gaussianWeight x*F x := by
    rw [←hcomp]
    exact MeasureTheory.integral_comp_exp (fun x : ℝ => gaussianWeight x*F x)
  refine ⟨hG,?_⟩
  rw [←hEq]
  have hi := integral_mono hLog hBig hDom
  rw [integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left hJ hc)

theorem uniform_left {F K : ℝ→ℝ} {M a1 A T J omegaBar U : ℝ}
    (ha1 : 0<a1) (hA : 1<A) (hAT : A≤T)
    (hF : Continuous F) (hFpos : ∀x>0,0≤F x)
    (hDom : ∀y:ℝ,logF F y≤(a1^2*(log T^3*T^((4:ℝ)/3)))*K y)
    (hK : Integrable K) (hJ : (∫y,K y)≤J)
    (hOmega : exp ((601/5000:ℝ)/(2*A^2))≤omegaBar)
    (hNum : 8*(601/5000:ℝ)*omegaBar*a1^2*J≤U)
    (hSmoothing : M≤(8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*
      (∫x in Ioi 0,gaussianWeight x*F x)) :
    M≤U*T^((4:ℝ)/3)*log T^3 := by
  have hT : 1<T := hA.trans_le hAT
  have hTp : 0<T := by linarith
  have hl := log_pos hT
  have hI := (source_gaussian ha1 hT hF hFpos hDom hK hJ).2
  have hIp : 0≤∫x in Ioi 0,gaussianWeight x*F x := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxp : 0<x := hx
    exact mul_nonneg (by unfold gaussianWeight;positivity) (hFpos x hxp)
  have hOmegaT := (omega_bound hA hAT).trans hOmega
  have hOp : 0≤omegaBar := le_trans (exp_pos _).le hOmega
  have hD : 0≤log T^3*T^((4:ℝ)/3) := by positivity
  calc
    M≤(8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*
      (∫x in Ioi 0,gaussianWeight x*F x) := hSmoothing
    _ ≤ (8*(601/5000:ℝ)*omegaBar)*(∫x in Ioi 0,gaussianWeight x*F x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hOmegaT (by norm_num)) hIp
    _ ≤ (8*(601/5000:ℝ)*omegaBar)*((a1^2*(log T^3*T^((4:ℝ)/3)))*J) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = (8*(601/5000:ℝ)*omegaBar*a1^2*J)*(log T^3*T^((4:ℝ)/3)) := by ring
    _ ≤ U*(log T^3*T^((4:ℝ)/3)) := mul_le_mul_of_nonneg_right hNum hD
    _ = _ := by ring

/-- The signed-log kernel premise is proved from raw Minkowski and the actual
anchor operands, so it cannot replace the desired U by an assumed majorant. -/
theorem raw_log_majorized {F : ℝ→ℝ} {a1 a2 m1 m2 A T low M1 M2 h r0 r1 : ℝ}
    (ha1 : 0<a1) (ha2 : 0≤a2) (hm1 : 0≤m1) (hm2 : 0≤m2)
    (hlow : 0≤low) (hFloor : 6*a1/exp 1+low≤a2)
    (hA : 1<A) (hAT : A≤T)
    (hM1 : m1≤M1) (hM2 : m2≤M2) (hh : 0<h) (hhA : h≤log A)
    (hr0 : a2/(a1*A^((1:ℝ)/6)*log A)≤r0)
    (hr1 : 1/(a1*A^((1:ℝ)/6)*log A*sqrt (log A))≤r1)
    (hRaw : ∀x>0,F x≤rawAmplitude a1 a2 m1 m2 T x^2) :
    ∀y:ℝ,logF F y≤(a1^2*(log T^3*T^((4:ℝ)/3)))*
      WinnerBetaA.SignedHeight.kernel M1 M2 h r0 r1 y := by
  intro y
  have hT : 1<T := hA.trans_le hAT
  have hTp : 0<T := by linarith
  have hlT := log_pos hT
  have hD : 0<log T^3*T^((4:ℝ)/3) := by positivity
  have hn := WinnerBetaA.SignedHeight.normalized_raw ha1 ha2 hm1 hm2 hlow hFloor hA hAT (exp_pos y)
  have hf := (hRaw (exp y) (exp_pos y)).trans ((div_le_iff₀ hD).mp hn)
  have hb := WinnerBetaA.SignedHeight.bracket_majorized ha1 ha2 hA (exp_pos y)
    hM1 hM2 hh hhA hr0 hr1
  have hp : 0≤WinnerBetaA.SignedHeight.bracket a1 a2 m1 m2 A (exp y) := by
    have hlA := log_pos hA
    have hAp : 0<A := by linarith
    unfold WinnerBetaA.SignedHeight.bracket
    positivity
  have hs := pow_le_pow_left₀ hp hb 2
  have he : (exp y)^((1:ℝ)/6)=exp (y/6) := by
    rw [rpow_def_of_pos (exp_pos y),log_exp]
    congr 1
    ring
  rw [log_exp,he,←exp_half] at hs
  have hmul := mul_le_mul_of_nonneg_left hs (show 0≤a1^2*(log T^3*T^((4:ℝ)/3)) by positivity)
  have hFc : F (exp y)≤(a1^2*(log T^3*T^((4:ℝ)/3)))*
      (sqrt (M1*exp y+M2)*(exp (y/6)*(1+max y 0/h)+r0)+r1*exp (y/2))^2 := by
    have heq : a1^2*WinnerBetaA.SignedHeight.bracket a1 a2 m1 m2 A (exp y)^2*
        (log T^3*T^((4:ℝ)/3))=
        (a1^2*(log T^3*T^((4:ℝ)/3)))*WinnerBetaA.SignedHeight.bracket a1 a2 m1 m2 A (exp y)^2 := by ring
    rw [heq] at hf
    exact hf.trans hmul
  have hw := mul_le_mul_of_nonneg_left hFc (exp_pos (2*y-(601/2500:ℝ)*exp (2*y))).le
  unfold logF WinnerBetaA.SignedHeight.kernel
  nlinarith

#print axioms raw_log_majorized

#print axioms source_gaussian
#print axioms uniform_left
end WinnerBetaA.DirectHeightMoment
