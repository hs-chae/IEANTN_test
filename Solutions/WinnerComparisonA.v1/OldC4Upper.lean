/- Copyright (c)2026 IEANTN contributors. Released under Apache2.0. -/
import StrongIntegrability
import WinnerBetaA.HeightSource
import WinnerBetaA.DirectHeightMoment
namespace WinnerOldC4Upper
open Real Set MeasureTheory WinnerBetaA.Minkowski WinnerBetaA.ActualObject
set_option maxHeartbeats 0

/-- The old C4 compression is valid for every admissible positive amplitude
floor. It is not restricted to the source's original numerical a2. -/
theorem raw_compression {A a3 m1 m2 T u t:ℝ}
    (ha3:0<a3) (hm1:0<m1) (hm2:0≤m2) (hT:0<T) (hu:0<u) (ht:0<t)
    (hA:a3≤A) :
    (A*sqrt ((m1*t+m2*T)*u)+sqrt t)^2≤
      (sqrt m1+1/(a3*sqrt u))^2*A^2*(t+(m2/m1)*T)*u := by
  let Q:ℝ:=t+(m2/m1)*T
  have hQ:0<Q:=by dsimp [Q];positivity
  have hAm:0≤A:=by linarith
  have hratio:0≤(m2/m1)*T:=by positivity
  have hmean:(m1*t+m2*T)*u=m1*(Q*u):=by dsimp [Q];field_simp <;> ring
  have hsqrt:sqrt ((m1*t+m2*T)*u)=sqrt m1*sqrt Q*sqrt u:=by
    rw [hmean,sqrt_mul hm1.le,sqrt_mul hQ.le]
    ring
  have htQ:sqrt t≤sqrt Q:=sqrt_le_sqrt (by dsimp [Q];linarith)
  have haone:1≤A/a3:=(one_le_div ha3).mpr hA
  have hsecond:sqrt t≤(A/a3)*sqrt Q:=
    htQ.trans (by nlinarith [mul_le_mul_of_nonneg_right haone (sqrt_nonneg Q)])
  have hb:A*sqrt ((m1*t+m2*T)*u)+sqrt t≤
      (sqrt m1+1/(a3*sqrt u))*A*sqrt Q*sqrt u:=by
    rw [hsqrt]
    calc
      _ ≤A*(sqrt m1*sqrt Q*sqrt u)+(A/a3)*sqrt Q:=add_le_add le_rfl hsecond
      _ =_:=by field_simp [ha3.ne',(sqrt_pos.2 hu).ne'] <;> ring
  have hh:=pow_le_pow_left₀ (by positivity:A*sqrt ((m1*t+m2*T)*u)+sqrt t≥0) hb 2
  have he:((sqrt m1+1/(a3*sqrt u))*A*sqrt Q*sqrt u)^2=
      (sqrt m1+1/(a3*sqrt u))^2*A^2*Q*u:=by
    simp only [mul_pow,sq_sqrt hQ.le,sq_sqrt hu.le]
  exact hh.trans_eq he

noncomputable def gaussianWeight (alpha x:ℝ) : ℝ :=x*exp (-2*alpha*x^2)
noncomputable def logF (alpha:ℝ) (F:ℝ→ℝ) (y:ℝ) : ℝ :=exp (2*y-2*alpha*exp (2*y))*F (exp y)

/-- Generic original smoothing-coordinate domination, with its exact
Jacobian and no assumed integrability of the actual source F. -/
theorem gaussian_from_log {alpha C:ℝ} {F K:ℝ→ℝ}
    (hC:0≤C) (hF:Continuous F) (hFpos:∀x>0,0≤F x)
    (hDom:∀y:ℝ,logF alpha F y≤C*K y) (hK:Integrable K) :
    IntegrableOn (fun x=>gaussianWeight alpha x*F x) (Ioi 0) ∧
      (∫x in Ioi 0,gaussianWeight alpha x*F x)≤C*(∫y,K y) := by
  have hBig:Integrable (fun y=>C*K y):=hK.const_mul C
  have hLog:Integrable (logF alpha F):=by
    apply hBig.mono' (show AEStronglyMeasurable (logF alpha F) volume by
      have hh:Continuous (logF alpha F):=by unfold logF;fun_prop
      exact hh.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun y=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤logF alpha F y by
        unfold logF;exact mul_nonneg (exp_pos _).le (hFpos _ (exp_pos y)))]
      exact hDom y
  have hcomp:(fun y:ℝ=>exp y • (gaussianWeight alpha (exp y)*F (exp y)))=logF alpha F:=by
    funext y
    have hp:(exp y)^2=exp (2*y):=by rw [pow_two,←exp_add];congr 1;ring
    have hw:exp y*gaussianWeight alpha (exp y)=exp (2*y-2*alpha*exp (2*y)):=by
      unfold gaussianWeight
      rw [show exp y*(exp y*exp (-2*alpha*(exp y)^2))=(exp y)^2*exp (-2*alpha*(exp y)^2) by ring,hp,←exp_add]
      congr 1
      ring
    change exp y*(gaussianWeight alpha (exp y)*F (exp y))=logF alpha F y
    unfold logF
    rw [←mul_assoc,hw]
  have hG:IntegrableOn (fun x=>gaussianWeight alpha x*F x) (Ioi 0):=by
    apply (MeasureTheory.integrable_comp_exp _).mp
    rw [hcomp]
    exact hLog
  refine ⟨hG,?_⟩
  have he:(∫y,logF alpha F y)=∫x in Ioi 0,gaussianWeight alpha x*F x:=by
    rw [←hcomp]
    exact MeasureTheory.integral_comp_exp (fun x:ℝ=>gaussianWeight alpha x*F x)
  rw [←he]
  have hi:=integral_mono hLog hBig hDom
  simpa only [integral_const_mul] using hi

open WinnerStrongC4Source

theorem amplitude_floor {t:ℝ} (ht:0<t) : a3≤a1*t^((1:ℝ)/6)*log t+a2 := by
  have hm:=power_log_minimum ht
  have ha:0≤a1:=by norm_num [a1]
  have hh:=mul_le_mul_of_nonneg_left hm ha
  unfold a2
  linear_combination a1*hm

theorem a2_admissible : 6*a1/exp 1+1461/1000≤a2 := by unfold a2 a3;linarith

theorem strong_raw_log {u:ℝ} (hu:0<u)
    (hRaw:∀x>0,scaledCriticalF (exp u) x≤
      rawAmplitude a1 a2 (mone u) (mtwo u) (exp u) x^2) :
    ∀y:ℝ,logF alpha (scaledCriticalF (exp u)) y≤
      (oldC4 u*exp ((4/3)*u)*u^3)*oldKernel u y := by
  intro y
  let A:ℝ:=a1*(exp y*exp u)^((1:ℝ)/6)*log (exp y*exp u)+a2
  have hA:a3≤A:=amplitude_floor (mul_pos (exp_pos _) (exp_pos _))
  have hr:rawAmplitude a1 a2 (mone u) (mtwo u) (exp u) (exp y)^2≤
      (sqrt (mone u)+1/(a3*sqrt u))^2*A^2*(exp y*exp u+(mtwo u/mone u)*exp u)*u:=by
    have hh:=raw_compression (by norm_num [a3]) (mone_pos hu) (mtwo_nonneg hu)
      (exp_pos u) hu (mul_pos (exp_pos y) (exp_pos u)) hA
    simpa only [rawAmplitude,A,log_exp,mul_assoc] using hh
  let bracket:ℝ:=exp (y/6)*(1+y/u)+oldRzero u
  have hpow:(exp y*exp u)^((1:ℝ)/6)=exp (y/6)*exp (u/6):=by
    rw [rpow_def_of_pos (mul_pos (exp_pos _) (exp_pos _)),log_mul (exp_ne_zero _) (exp_ne_zero _),log_exp,log_exp,←exp_add]
    congr 1
    ring
  have hAmp:A=a1*exp (u/6)*u*bracket:=by
    dsimp [A,bracket]
    rw [hpow,log_mul (exp_ne_zero _) (exp_ne_zero _),log_exp,log_exp]
    unfold oldRzero
    field_simp [hu.ne',show a1≠0 by norm_num [a1],exp_ne_zero]
    <;> ring
  have hscale:exp (u/6)^2*exp u=exp ((4/3)*u):=by
    rw [pow_two,←exp_add,←exp_add]
    congr 1
    ring
  have hcompressed:scaledCriticalF (exp u) (exp y)≤
      (oldC4 u*exp ((4/3)*u)*u^3)*bracket^2*(exp y+oldRatio u):=by
    apply ((hRaw (exp y) (exp_pos y)).trans hr).trans_eq
    rw [hAmp]
    calc
      _ =oldC4 u*(exp (u/6)^2*exp u)*u^3*bracket^2*(exp y+oldRatio u):=by
        unfold oldC4 oldRatio
        ring
      _ =_:=by rw [hscale]
  have hh:=mul_le_mul_of_nonneg_left hcompressed (exp_pos (2*y-2*alpha*exp (2*y))).le
  unfold logF oldKernel
  dsimp only [bracket] at hh
  convert! hh using 1 <;> ring

/-- Actual original smoothing weight at the rival's alpha, rather than the
new construction's fixed0.1202 weight. -/
noncomputable def oldWeight (T:ℝ) (s:ℂ) : ℂ :=
  ((s-1)/s)*Complex.exp ((alpha:ℂ)*(s/(T:ℂ))^2)
noncomputable def oldMoment (T sigma:ℝ) : ℝ :=
  ∫t:ℝ,‖oldWeight T (vertical sigma t)*mollifiedError T (vertical sigma t)‖^2
/-- The original Gaussian smoothing primitive, instantiated at alpha0.11855.
It assumes neither the oldU budget nor any density/count/prime bound. -/
def OriginalSmoothingAt (T:ℝ) : Prop :=
  oldMoment T (1/2)≤(8*alpha*exp (alpha/(2*T^2)))*
    (∫x in Ioi 0,gaussianWeight alpha x*scaledCriticalF T x)

theorem exact_mean_operands (u:ℝ) :
    mone u=WinnerBetaA.HeightSource.meanOne (exp u) ∧
    mtwo u=WinnerBetaA.HeightSource.meanTwo (exp u) := by
  constructor
  · simp [mone,WinnerBetaA.HeightSource.meanOne]
  · unfold mtwo WinnerBetaA.HeightSource.meanTwo
    simp only [log_exp,exp_neg]
    change Real.pi*mzero*(31/50)/u+6*mzero/Real.pi*(exp u)⁻¹+
      Real.pi*mzero*(131/125)*(exp u)⁻¹/u=
      Real.pi*mzero*(31/50)/u+6*mzero/(Real.pi*exp u)+Real.pi*mzero*(131/125)/(exp u*u)
    ring

/-- A genuine old-C4 upper moment from shared original low/high zeta and
exact-T mean-square inputs plus the independently named original smoothing
primitive at the old alpha. The inflated a2 is proved admissible. -/
theorem actual_old_moment {u:ℝ} (hu:WinnerOldFloors.h≤u)
    (hLow:∀t:ℝ,0≤t→t≤3→‖riemannZeta (vertical (1/2) t)‖≤(1461/1000:ℝ))
    (hHigh:∀t:ℝ,3≤t→‖riemannZeta (vertical (1/2) t)‖≤(611/1000)*t^((1:ℝ)/6)*log t)
    (hMean:∀t>0,(∫v in (0:ℝ)..t,‖mollifier (exp u) (vertical (1/2) v)‖^2)≤
      (WinnerBetaA.HeightSource.meanOne (exp u)*t+
        WinnerBetaA.HeightSource.meanTwo (exp u)*exp u)*log (exp u))
    (hSmoothing:OriginalSmoothingAt (exp u)) :
    oldMoment (exp u) (1/2)≤oldU u*exp ((4/3)*u)*u^3 := by
  have hup:0<u:=by linarith [WinnerOldFloors.h_lower.trans hu]
  obtain ⟨hone,htwo⟩:=exact_mean_operands u
  have hRaw:=WinnerBetaA.HeightSource.raw_from_mean
    (T:=exp u) (a1:=a1) (a2:=a2) (m1:=mone u) (m2:=mtwo u)
    (exp_pos u) (by norm_num [a1]) a2_admissible hLow
    (by simpa only [a1] using hHigh) (by
      intro t ht
      rw [hone,htwo]
      exact hMean t ht)
  have hC:0≤oldC4 u*exp ((4/3)*u)*u^3:=by unfold oldC4;positivity
  have hI:=(gaussian_from_log hC (scaledCriticalF_continuous (exp u))
    (fun x hx=>scaledCriticalF_nonneg (exp_pos u).le hx.le)
    (strong_raw_log hup hRaw) (oldKernel_integrable hu)).2
  have hcoef:0≤8*alpha*exp (alpha/(2*(exp u)^2)):=by unfold alpha;positivity
  have hh:=hSmoothing.trans (mul_le_mul_of_nonneg_left hI hcoef)
  have he:(exp u)^2=exp (2*u):=by rw [pow_two,←exp_add];congr 1;ring
  unfold oldU
  rw [he] at hh
  convert! hh using 1 <;> ring

/-- Physical-height version, using exactly the shared source mean-square
operands. The alpha-specific smoothing relation remains explicitly named. -/
theorem actual_old_moment_at_T {T:ℝ} (hHT:WinnerOriginalScalars.height≤T)
    (hLow:∀t:ℝ,0≤t→t≤3→‖riemannZeta (vertical (1/2) t)‖≤(1461/1000:ℝ))
    (hHigh:∀t:ℝ,3≤t→‖riemannZeta (vertical (1/2) t)‖≤(611/1000)*t^((1:ℝ)/6)*log t)
    (hMean:∀t>0,(∫v in (0:ℝ)..t,‖mollifier T (vertical (1/2) v)‖^2)≤
      (WinnerBetaA.HeightSource.meanOne T*t+WinnerBetaA.HeightSource.meanTwo T*T)*log T)
    (hSmoothing:OriginalSmoothingAt T) :
    oldMoment T (1/2)≤oldU (log T)*T^((4:ℝ)/3)*log T^3 := by
  have hT:0<T:=lt_of_lt_of_le (by norm_num [WinnerOriginalScalars.height]) hHT
  have hu:WinnerOldFloors.h≤log T:=by
    exact log_le_log (by norm_num : (0:ℝ)<3000000000000) hHT
  have hh:=actual_old_moment hu hLow hHigh
    (by intro t ht;simpa only [exp_log hT] using hMean t ht)
    (by simpa only [exp_log hT] using hSmoothing)
  have he:exp ((4/3)*log T)=T^((4:ℝ)/3):=by
    rw [rpow_def_of_pos hT]
    congr 1
    ring
  simpa only [exp_log hT,he] using hh
#print axioms actual_old_moment_at_T
#check actual_old_moment_at_T

#print axioms actual_old_moment

#print axioms raw_compression
#print axioms strong_raw_log
end WinnerOldC4Upper
