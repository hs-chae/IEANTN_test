/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerBetaA.ParamSource
import OriginalRightMoment
namespace WinnerBetaA.HeightSource
open Real Set MeasureTheory
open WinnerBetaA.Minkowski WinnerBetaA.ActualObject WinnerOriginalScalars
set_option maxHeartbeats 0

/-- KLN4.1 proof before replacing X by its minimum. Here X=T exactly. -/
noncomputable def meanOne (T : ℝ) : ℝ := 6/Real.pi^2+(131/125)/log T
noncomputable def meanTwo (T : ℝ) : ℝ :=
  Real.pi*sourceM0*(31/50)/log T+6*sourceM0/(Real.pi*T)+
    Real.pi*sourceM0*(131/125)/(T*log T)

/-- Actual pre-uniformization right-moment source operands, for arbitrary delta. -/
noncomputable def rightFive (gamma delta T : ℝ) : ℝ :=
  Real.pi*sourceM0*(529/1000)/(2*delta)*
    (1+2*delta/log T)^2*exp (2*delta*gamma/log T)
noncomputable def rightSix (delta T : ℝ) : ℝ :=
  (529/1000)/(5*delta*exp delta)*(1+delta/log T)^2+
    (121/200)*exp (-2*delta)/(log T)^2
noncomputable def rightV (gamma delta T : ℝ) : ℝ :=
  8*(601/5000)*exp (2*(601/5000)*((1+delta/log T)/T)^2)*
    ((rightFive gamma delta T+rightSix delta T*Real.pi*sourceM0/T)/(4*(601/5000))+
      rightSix delta T*sqrt Real.pi/(8*(601/5000)*sqrt (2*(601/5000))))

theorem meanOne_nonneg {T : ℝ} (hT : 1<T) : 0≤meanOne T := by
  have hl := log_pos hT
  unfold meanOne
  positivity

theorem meanTwo_nonneg {T : ℝ} (hT : 1<T) : 0≤meanTwo T := by
  have hl := log_pos hT
  have ht : 0<T := by linarith
  have hm := source_mzero_pos
  unfold meanTwo
  positivity

theorem meanOne_mono {A T : ℝ} (hA : 1<A) (hAT : A≤T) : meanOne T≤meanOne A := by
  have hAp : 0<A := by linarith
  have hlA : 0<log A := log_pos hA
  have hlT : 0<log T := hlA.trans_le (log_le_log hAp hAT)
  unfold meanOne
  gcongr

theorem meanTwo_mono {A T : ℝ} (hA : 1<A) (hAT : A≤T) : meanTwo T≤meanTwo A := by
  have hAp : 0<A := by linarith
  have hTp : 0<T := hAp.trans_le hAT
  have hlA : 0<log A := log_pos hA
  have hlAT := log_le_log hAp hAT
  have hlT : 0<log T := hlA.trans_le hlAT
  have hm := source_mzero_pos
  unfold meanTwo
  gcongr

theorem rightFive_nonneg {gamma delta T : ℝ} (hd : 0<delta) : 0≤rightFive gamma delta T := by
  have hm := source_mzero_pos
  unfold rightFive
  positivity

theorem rightSix_nonneg {delta T : ℝ} (hd : 0<delta) : 0≤rightSix delta T := by
  unfold rightSix
  positivity

theorem rightFive_uniform {gamma delta A T : ℝ}
    (hg : gamma≤1) (hd : 0<delta) (hA : 1<A) (hAT : A≤T) :
    rightFive gamma delta T≤rightFive 1 delta A := by
  have hAp : 0<A := by linarith
  have hlA := log_pos hA
  have hlAT := log_le_log hAp hAT
  have hlT := hlA.trans_le hlAT
  have hm := source_mzero_pos
  have he : 2*delta*gamma/log T≤2*delta/log A := by
    apply (div_le_div_of_nonneg_right (by nlinarith : 2*delta*gamma≤2*delta) hlT.le).trans
    exact div_le_div_of_nonneg_left (by positivity) hlA hlAT
  unfold rightFive
  apply mul_le_mul _ (exp_le_exp.mpr (by simpa using he)) (by positivity) (by positivity)
  gcongr

theorem rightSix_uniform {delta A T : ℝ} (hd : 0<delta) (hA : 1<A) (hAT : A≤T) :
    rightSix delta T≤rightSix delta A := by
  have hAp : 0<A := by linarith
  have hlA := log_pos hA
  have hlAT := log_le_log hAp hAT
  have hlT := hlA.trans_le hlAT
  unfold rightSix
  gcongr

theorem rightV_uniform {gamma delta A T : ℝ}
    (hg : gamma≤1) (hd : 0<delta) (hA : 1<A) (hAT : A≤T) :
    rightV gamma delta T≤rightV 1 delta A := by
  have hAp : 0<A := by linarith
  have hTp : 0<T := hAp.trans_le hAT
  have hlA := log_pos hA
  have hlAT := log_le_log hAp hAT
  have hlT := hlA.trans_le hlAT
  have hm := source_mzero_pos
  have hc5 := rightFive_uniform hg hd hA hAT
  have hc6 := rightSix_uniform hd hA hAT
  have hp5 := rightFive_nonneg (gamma:=gamma) (T:=T) hd
  have hp6 := rightSix_nonneg (T:=T) hd
  have hp6A := rightSix_nonneg (T:=A) hd
  have he : exp (2*(601/5000)*((1+delta/log T)/T)^2)≤
      exp (2*(601/5000)*((1+delta/log A)/A)^2) := by
    apply exp_le_exp.mpr
    gcongr
  unfold rightV
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · exact mul_le_mul_of_nonneg_left he (by norm_num)
  · gcongr

noncomputable def heightKernel (M1 M2 h r0 r1 y : ℝ) : ℝ :=
  exp (2*y-(601/2500:ℝ)*exp (2*y))*
    (sqrt (M1*exp y+M2)*(exp (y/6)*(1+|y|/h)+r0)+r1*exp (y/2))^2

theorem logKernel_le_heightKernel {a1 a2 m1 m2 A M1 M2 h r0 r1 : ℝ}
    (ha1 : 0<a1) (ha2 : 0≤a2) (hA : 1<A)
    (hm1 : m1≤M1) (hm2 : m2≤M2) (hh : 0<h) (hhA : h≤log A)
    (hr0 : a2/(a1*A^((1:ℝ)/6)*log A)≤r0)
    (hr1 : 1/(a1*A^((1:ℝ)/6)*log A*sqrt (log A))≤r1) :
    ∀y:ℝ, logKernel a1 a2 m1 m2 A y≤heightKernel M1 M2 h r0 r1 y := by
  intro y
  have hb := bracket_of_scalar_bounds ha1 ha2 hA (exp_pos y) hm1 hm2 hh hhA hr0 hr1
  have hkn : 0≤kernelBracket a1 a2 m1 m2 A (exp y) := by
    have hl := log_pos hA
    have hp : 0<A := by linarith
    unfold kernelBracket
    positivity
  have hs := pow_le_pow_left₀ hkn hb 2
  rw [envelopeBracket_exp] at hs
  exact mul_le_mul_of_nonneg_left hs (exp_pos _).le

/-- Exact T-dependent source mean-square is monotone-enlarged only at the
chosen height anchor; no globally pinned m1/m2 loss is forced. -/
theorem mean_square_anchor {T A : ℝ} (hA : 1<A) (hAT : A≤T)
    (hMean : ∀t>0,(∫u in (0:ℝ)..t,‖mollifier T (vertical (1/2) u)‖^2)≤
      (meanOne T*t+meanTwo T*T)*log T) :
    ∀t>0,(∫u in (0:ℝ)..t,‖mollifier T (vertical (1/2) u)‖^2)≤
      (meanOne A*t+meanTwo A*T)*log T := by
  intro t ht
  have hT : 1<T := hA.trans_le hAT
  have hTp : 0<T := by linarith
  have hl : 0≤log T := (log_pos hT).le
  have h1 := mul_le_mul_of_nonneg_right (meanOne_mono hA hAT) ht.le
  have h2 := mul_le_mul_of_nonneg_right (meanTwo_mono hA hAT) hTp.le
  exact (hMean t ht).trans (mul_le_mul_of_nonneg_right (add_le_add h1 h2) hl)

theorem rightFive_uniform_to {gamma gammaBar delta A T : ℝ}
    (hg : gamma≤gammaBar) (hg0 : 0≤gammaBar) (hd : 0<delta) (hA : 1<A) (hAT : A≤T) :
    rightFive gamma delta T≤rightFive gammaBar delta A := by
  have hAp : 0<A := by linarith
  have hlA := log_pos hA
  have hlAT := log_le_log hAp hAT
  have hlT := hlA.trans_le hlAT
  have hm := source_mzero_pos
  have he : 2*delta*gamma/log T≤2*delta*gammaBar/log A := by
    apply (div_le_div_of_nonneg_right (by nlinarith : 2*delta*gamma≤2*delta*gammaBar) hlT.le).trans
    exact div_le_div_of_nonneg_left (by positivity) hlA hlAT
  unfold rightFive
  apply mul_le_mul _ (exp_le_exp.mpr he) (by positivity) (by positivity)
  gcongr

theorem rightV_uniform_to {gamma gammaBar delta A T : ℝ}
    (hg : gamma≤gammaBar) (hg0 : 0≤gammaBar) (hd : 0<delta) (hA : 1<A) (hAT : A≤T) :
    rightV gamma delta T≤rightV gammaBar delta A := by
  have hAp : 0<A := by linarith
  have hTp : 0<T := hAp.trans_le hAT
  have hlA := log_pos hA
  have hlAT := log_le_log hAp hAT
  have hlT := hlA.trans_le hlAT
  have hm := source_mzero_pos
  have hc5 := rightFive_uniform_to hg hg0 hd hA hAT
  have hc6 := rightSix_uniform hd hA hAT
  have hp5 := rightFive_nonneg (gamma:=gamma) (T:=T) hd
  have hp6 := rightSix_nonneg (T:=T) hd
  have hp6A := rightSix_nonneg (T:=A) hd
  have he : exp (2*(601/5000)*((1+delta/log T)/T)^2)≤
      exp (2*(601/5000)*((1+delta/log A)/A)^2) := by
    apply exp_le_exp.mpr
    gcongr
  unfold rightV
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · exact mul_le_mul_of_nonneg_left he (by norm_num)
  · gcongr

/-- All mean-square operands are generic here; the exact-X provider later
supplies m1=meanOne(A),m2=meanTwo(A) from its actual T-dependent source. -/
theorem raw_from_mean {T a1 a2 low m1 m2 : ℝ}
    (hT : 0<T) (ha1 : 0≤a1) (hFloor : 6*a1/exp 1+low≤a2)
    (hLow : ∀u:ℝ,0≤u→u≤3→‖riemannZeta (vertical (1/2) u)‖≤low)
    (hHigh : ∀u:ℝ,3≤u→‖riemannZeta (vertical (1/2) u)‖≤a1*u^((1:ℝ)/6)*log u)
    (hMean : ∀t>0,(∫u in (0:ℝ)..t,‖mollifier T (vertical (1/2) u)‖^2)≤
      (m1*t+m2*T)*log T) :
    ∀x>0,scaledCriticalF T x≤rawAmplitude a1 a2 m1 m2 T x^2 := by
  intro x hx
  have ht : 0<x*T := mul_pos hx hT
  have hZ : ∀u∈Icc 0 (x*T),‖riemannZeta (vertical (1/2) u)‖≤a1*(x*T)^((1:ℝ)/6)*log (x*T)+a2 :=
    fun u hu => zeta_on_initial_interval_param ha1 hFloor hLow hHigh ht hu
  have hB : 0≤a1*(x*T)^((1:ℝ)/6)*log (x*T)+a2 :=
    (norm_nonneg _).trans (hZ 0 ⟨le_rfl,ht.le⟩)
  have hh := integral_minkowski_sub_one ht critical_zeta_continuous
    ((mollifier_continuous T).comp (vertical_continuous (1/2))) hB hZ (hMean (x*T) ht)
  simpa only [scaledCriticalF,cumulativeSquare,mollifiedError,rawAmplitude,
    Function.comp_apply,mul_assoc] using hh

/-- The source's negative C6 exponential is preserved in the source identity;
its later removal is a separately proved upper relaxation. -/
noncomputable def rightSixExact (gamma delta T : ℝ) : ℝ :=
  (529/1000)/(5*delta*exp delta)*(1+delta/log T)^2*
    exp (delta*(gamma-log 5)/log T)+(121/200)*exp (-2*delta)/(log T)^2
noncomputable def rightVExact (gamma delta T : ℝ) : ℝ :=
  8*(601/5000)*exp (2*(601/5000)*((1+delta/log T)/T)^2)*
    ((rightFive gamma delta T+rightSixExact gamma delta T*Real.pi*sourceM0/T)/(4*(601/5000))+
      rightSixExact gamma delta T*sqrt Real.pi/(8*(601/5000)*sqrt (2*(601/5000))))

theorem rightSixExact_le {gamma delta T : ℝ} (hg : gamma≤1) (hd : 0<delta) (hT : 1<T) :
    rightSixExact gamma delta T≤rightSix delta T := by
  have hl := log_pos hT
  have hlog5 : (1:ℝ)≤log 5 := by
    apply exp_le_exp.mp
    rw [exp_log (by norm_num : (0:ℝ)<5)]
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have he : exp (delta*(gamma-log 5)/log T)≤1 := exp_le_one_iff.mpr (by
    apply div_nonpos_of_nonpos_of_nonneg _ hl.le
    exact mul_nonpos_of_nonneg_of_nonpos hd.le (by linarith))
  have hp : 0≤(529/1000:ℝ)/(5*delta*exp delta)*(1+delta/log T)^2 := by positivity
  have hh := mul_le_mul_of_nonneg_left he hp
  unfold rightSixExact rightSix
  nlinarith

theorem rightVExact_le {gamma delta T : ℝ} (hg : gamma≤1) (hd : 0<delta) (hT : 1<T) :
    rightVExact gamma delta T≤rightV gamma delta T := by
  have hm := source_mzero_pos
  have ht : 0<T := by linarith
  have hc := rightSixExact_le hg hd hT
  unfold rightVExact rightV
  gcongr

#print axioms rightVExact_le

#print axioms rightV_uniform_to
#print axioms raw_from_mean

#print axioms mean_square_anchor
#print axioms rightV_uniform
#print axioms logKernel_le_heightKernel
end WinnerBetaA.HeightSource
