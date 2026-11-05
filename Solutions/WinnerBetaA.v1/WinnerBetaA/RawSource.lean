/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.ActualObject
import OriginalAmplitude

namespace WinnerBetaA.ActualObject
open Real Set MeasureTheory
open WinnerOriginalScalars WinnerBetaA.Minkowski
set_option maxHeartbeats 0

/-- The elementary minimum is global on the analytic domain t>0. -/
theorem power_log_minimum {t : ℝ} (ht : 0 < t) :
    -(6:ℝ)/exp 1 ≤ t^((1:ℝ)/6)*log t := by
  have h := Real.mul_exp_neg_le_exp_neg_one (-log t/6)
  have he : Real.exp (-(-log t/6)) = t^((1:ℝ)/6) := by
    rw [rpow_def_of_pos ht]
    congr 1
    ring
  rw [he,exp_neg] at h
  calc
    -(6:ℝ)/exp 1 = -6*(exp 1)⁻¹ := by ring
    _ ≤ -6*((-log t/6)*t^((1:ℝ)/6)) :=
      mul_le_mul_of_nonpos_left h (by norm_num)
    _ = _ := by ring

/-- The rational a2 adjustment is derived from an actual finite certificate. -/
theorem amplitude_at_least_low {t : ℝ} (ht : 0 < t) :
    (1461/1000:ℝ) ≤ (309/500)*t^((1:ℝ)/6)*log t+1413/500 := by
  linear_combination (309/500:ℝ)*(power_log_minimum ht)+amplitude_floor_upper

theorem power_log_monotone : MonotoneOn (fun t : ℝ => t^((1:ℝ)/6)*log t) (Ici 1) := by
  intro s hs t ht hst
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hlog : 0 ≤ log s := log_nonneg hs
  have hpow : s^((1:ℝ)/6) ≤ t^((1:ℝ)/6) :=
    rpow_le_rpow hs0.le hst (by norm_num)
  have hl : log s ≤ log t := log_le_log hs0 hst
  exact mul_le_mul hpow hl hlog (rpow_nonneg (by linarith : 0≤t) _)

/-- The exact low/high primary-source premises suffice for the source's entire
interval supremum, including u=0.  No small-t evaluation oracle is assumed. -/
theorem zeta_on_initial_interval
    (hLow : ∀ u : ℝ, 0 ≤ u → u ≤ 3 →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ (1461/1000:ℝ))
    (hHPY : ∀ u : ℝ, 3 ≤ u →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ (309/500)*u^((1:ℝ)/6)*log u)
    {t u : ℝ} (ht : 0 < t) (hu : u ∈ Icc 0 t) :
    ‖riemannZeta (vertical (1/2) u)‖ ≤ (309/500)*t^((1:ℝ)/6)*log t+1413/500 := by
  by_cases hsmall : u ≤ 3
  · exact (hLow u hu.1 hsmall).trans (amplitude_at_least_low ht)
  · have hu3 : 3 ≤ u := le_of_lt (lt_of_not_ge hsmall)
    have htu : u^((1:ℝ)/6)*log u ≤ t^((1:ℝ)/6)*log t :=
      power_log_monotone (by change 1≤u; linarith) (by change 1≤t; linarith [hu.2]) hu.2
    have hh := mul_le_mul_of_nonneg_left htu (by norm_num : (0:ℝ)≤309/500)
    linarith [hHPY u hu3]

/-- Integral Cauchy--Schwarz against 1 on an actual finite interval.  The
proof integrates a nonnegative square and explicitly establishes convergence. -/
theorem integral_le_sqrt_square {f : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t) (hf : Continuous f) (hpos : ∀ u ∈ Icc 0 t, 0 ≤ f u) :
    (∫ u in (0:ℝ)..t, f u) ≤ sqrt (∫ u in (0:ℝ)..t, (f u)^2)*sqrt t := by
  let I : ℝ := ∫ u in (0:ℝ)..t, f u
  let Q : ℝ := ∫ u in (0:ℝ)..t, (f u)^2
  let c : ℝ := I/t
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg ht.le hpos
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg_of_forall ht.le (by intro u; positivity)
  have hs : 0 ≤ ∫ u in (0:ℝ)..t, (f u-c)^2 :=
    intervalIntegral.integral_nonneg_of_forall ht.le (by intro u; positivity)
  have he : (∫ u in (0:ℝ)..t, (f u-c)^2) = Q-2*c*I+c^2*t := by
    calc
      _ = ∫ u in (0:ℝ)..t, (f u)^2-(2*c)*f u+c^2 := by
        apply intervalIntegral.integral_congr
        intro u hu
        ring
      _ = _ := by
        have h2 : IntervalIntegrable (fun u => (f u)^2) volume 0 t :=
          (hf.pow 2).intervalIntegrable _ _
        have hcF : IntervalIntegrable (fun u => (2*c)*f u) volume 0 t :=
          (hf.const_mul _).intervalIntegrable _ _
        have hconst : IntervalIntegrable (fun _ : ℝ => c^2) volume 0 t :=
          continuous_const.intervalIntegrable _ _
        rw [intervalIntegral.integral_add (h2.sub hcF) hconst]
        rw [intervalIntegral.integral_sub h2 hcF,intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [sub_zero,smul_eq_mul]
        dsimp only [Q,I]
        ring
  rw [he] at hs
  have heq : t*(Q-2*c*I+c^2*t)=t*Q-I^2 := by
    dsimp only [c]
    field_simp [ht.ne']
    <;> ring
  have hsq := mul_nonneg ht.le hs
  rw [heq] at hsq
  have hst := Real.sq_sqrt ht.le
  have hsQ := Real.sq_sqrt hQ
  have hprod : (sqrt Q*sqrt t)^2 = t*Q := by
    rw [mul_pow,hsQ,hst]
    ring
  have hp : 0 ≤ sqrt Q*sqrt t := by positivity
  nlinarith

/-- The L2 triangle step is proved directly by finite-interval integration,
rather than added as a new majorant hypothesis. -/
theorem integral_minkowski_sub_one {z m : ℝ → ℂ} {t B Qbar : ℝ}
    (ht : 0 < t) (hz : Continuous z) (hm : Continuous m) (hB : 0 ≤ B)
    (hZ : ∀ u ∈ Icc 0 t, ‖z u‖ ≤ B)
    (hMean : (∫ u in (0:ℝ)..t, ‖m u‖^2) ≤ Qbar) :
    (∫ u in (0:ℝ)..t, ‖z u*m u-1‖^2) ≤ (B*sqrt Qbar+sqrt t)^2 := by
  let Q : ℝ := ∫ u in (0:ℝ)..t, ‖m u‖^2
  let I : ℝ := ∫ u in (0:ℝ)..t, ‖m u‖
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg_of_forall ht.le (by intro u; positivity)
  have hQbar : 0 ≤ Qbar := hQ.trans hMean
  have hCS : I ≤ sqrt Q*sqrt t :=
    integral_le_sqrt_square ht hm.norm (by intro u hu; positivity)
  have hSQ : sqrt Q ≤ sqrt Qbar := Real.sqrt_le_sqrt hMean
  have hmain : (∫ u in (0:ℝ)..t, ‖z u*m u-1‖^2) ≤
      ∫ u in (0:ℝ)..t, (B*‖m u‖+1)^2 := by
    apply intervalIntegral.integral_mono_on ht.le
      ((((hz.mul hm).sub continuous_const).norm.pow 2).intervalIntegrable _ _)
      ((((hm.norm.const_mul B).add continuous_const).pow 2).intervalIntegrable _ _)
    intro u hu
    have hnorm : ‖z u*m u-1‖ ≤ B*‖m u‖+1 := by
      have hh := norm_sub_le (z u*m u) (1:ℂ)
      rw [norm_mul,norm_one] at hh
      have hm' := mul_le_mul_of_nonneg_right (hZ u hu) (norm_nonneg (m u))
      linarith
    change ‖z u*m u-1‖^2 ≤ (B*‖m u‖+1)^2
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have he : (∫ u in (0:ℝ)..t, (B*‖m u‖+1)^2) = B^2*Q+2*B*I+t := by
    calc
      _ = ∫ u in (0:ℝ)..t, B^2*‖m u‖^2+(2*B)*‖m u‖+1 := by
        apply intervalIntegral.integral_congr
        intro u hu
        ring
      _ = _ := by
        have h2 : IntervalIntegrable (fun u => B^2*‖m u‖^2) volume 0 t :=
          ((hm.norm.pow 2).const_mul (B^2)).intervalIntegrable _ _
        have h1 : IntervalIntegrable (fun u => (2*B)*‖m u‖) volume 0 t :=
          (hm.norm.const_mul (2*B)).intervalIntegrable _ _
        have hc : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 t :=
          continuous_const.intervalIntegrable _ _
        rw [intervalIntegral.integral_add (h2.add h1) hc,
          intervalIntegral.integral_add h2 h1,intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
        simp only [sub_zero,smul_eq_mul,mul_one]
        rfl
  have hcross : 2*B*I ≤ 2*B*(sqrt Q*sqrt t) :=
    mul_le_mul_of_nonneg_left hCS (by positivity)
  have hsqQ : (sqrt Q)^2=Q := Real.sq_sqrt hQ
  have hsqt : (sqrt t)^2=t := Real.sq_sqrt ht.le
  have hfirst : B^2*Q+2*B*I+t ≤ (B*sqrt Q+sqrt t)^2 := by
    nlinarith
  have hlast : (B*sqrt Q+sqrt t)^2 ≤ (B*sqrt Qbar+sqrt t)^2 := by
    have hh := mul_le_mul_of_nonneg_left hSQ hB
    have hsum : B*sqrt Q+sqrt t ≤ B*sqrt Qbar+sqrt t := by linarith
    exact pow_le_pow_left₀ (show 0 ≤ B*sqrt Q+sqrt t by positivity)
      hsum 2
  exact hmain.trans (he.le.trans (hfirst.trans hlast))

theorem critical_zeta_continuous :
    Continuous (fun u : ℝ => riemannZeta (vertical (1/2) u)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have hs : vertical (1/2) u ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [vertical] at hr
  exact (differentiableAt_riemannZeta hs).continuousAt.comp
    (vertical_continuous (1/2)).continuousAt

/-- Raw Minkowski follows from the independently published zeta inputs and
the actual source mean-square mollifier estimate. -/
theorem raw_of_zeta_and_mean_square {T : ℝ}
    (hHT : height ≤ T)
    (hLow : ∀ u : ℝ, 0 ≤ u → u ≤ 3 →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ (1461/1000:ℝ))
    (hHPY : ∀ u : ℝ, 3 ≤ u →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ (309/500)*u^((1:ℝ)/6)*log u)
    (hMeanSquare : ∀ t > 0, (∫ u in (0:ℝ)..t, ‖mollifier T (vertical (1/2) u)‖^2) ≤
      (sourceM1*t+sourceM2*T)*log T) :
    ∀ x > 0, scaledCriticalF T x ≤
      rawAmplitude (309/500) (1413/500) sourceM1 sourceM2 T x ^ 2 := by
  intro x hx
  have hT : 0 < T := lt_of_lt_of_le (by norm_num [height]) hHT
  have ht : 0 < x*T := mul_pos hx hT
  have hB : 0 ≤ (309/500:ℝ)*(x*T)^((1:ℝ)/6)*log (x*T)+1413/500 :=
    le_trans (by norm_num) (amplitude_at_least_low ht)
  have hh := integral_minkowski_sub_one ht critical_zeta_continuous
    ((mollifier_continuous T).comp (vertical_continuous (1/2))) hB
    (fun u hu => zeta_on_initial_interval hLow hHPY ht hu) (hMeanSquare (x*T) ht)
  simpa only [scaledCriticalF,cumulativeSquare,mollifiedError,rawAmplitude,
    Function.comp_apply,mul_assoc] using hh

/-- All newly introduced U steps, including raw Minkowski and a2 rounding,
are now proved.  These four premises are independently attributed source
theorems, not assumptions of the desired improved moment or prime error. -/
theorem actual_left_U134_from_primary_inputs {T : ℝ}
    (hHT : height ≤ T)
    (hLow : ∀ u : ℝ, 0 ≤ u → u ≤ 3 →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ (1461/1000:ℝ))
    (hHPY : ∀ u : ℝ, 3 ≤ u →
      ‖riemannZeta (vertical (1/2) u)‖ ≤ (309/500)*u^((1:ℝ)/6)*log u)
    (hMeanSquare : ∀ t > 0, (∫ u in (0:ℝ)..t, ‖mollifier T (vertical (1/2) u)‖^2) ≤
      (sourceM1*t+sourceM2*T)*log T)
    (hSourceSmoothing : sourceMoment T (1/2) ≤
      (8*(601/5000:ℝ)*Real.exp ((601/5000:ℝ)/(2*T^2)))*
        (∫ x in Ioi 0, gaussianWeight x * scaledCriticalF T x)) :
    sourceMoment T (1/2) ≤ (67/50:ℝ)*T^((4:ℝ)/3)*Real.log T^3 := by
  exact actual_source_left_U134 hHT
    (raw_of_zeta_and_mean_square hHT hLow hHPY hMeanSquare) hSourceSmoothing

#print axioms power_log_minimum
#print axioms zeta_on_initial_interval
#print axioms integral_le_sqrt_square
#print axioms integral_minkowski_sub_one
#print axioms raw_of_zeta_and_mean_square
#print axioms actual_left_U134_from_primary_inputs
end WinnerBetaA.ActualObject
