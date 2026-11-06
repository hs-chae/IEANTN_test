/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.Interval.MomentOrder
import E1FrozenN.Interval.RayDecay

open Real Set MeasureTheory
namespace E1FrozenN.Interval

noncomputable def p (s : ℝ) : ℝ := 8*(1-s)/3
noncomputable def q (s : ℝ) : ℝ := 5-2*s
noncomputable def b (s : ℝ) : ℝ := 1-p s
noncomputable def rate (s : ℝ) : ℝ := 7*(1-s)/15
noncomputable def ulog (L : ℝ) : ℝ := L/5+log k
noncomputable def factor4 (s u : ℝ) : ℝ :=
  1+q s/(b s*u)+q s*(q s-1)/(b s*u)^2+
    q s*(q s-1)*(q s-2)/(b s*u)^3+
    q s*(q s-1)*(q s-2)*(q s-3)/(b s*u)^4
noncomputable def factor2 (u : ℝ) : ℝ := 1+2/u+2/u^2

noncomputable def mainRay (s L : ℝ) : ℝ :=
  (2*(9795/1000 : ℝ)*exp (p s*log k)/b s)*
    (L*exp (-rate s*L)*(ulog L)^(q s))*factor4 s (ulog L)
noncomputable def correctionRay (s L : ℝ) : ℝ :=
  (2*(4465/1000 : ℝ))*(L*exp (-(1-s)*L)*(ulog L)^2)*factor2 (ulog L)
noncomputable def integrand (L s : ℝ) : ℝ :=
  2*k*L*exp (L/5)*exp (-(1-s)*L)*moment s (U L)

theorem U_pos (L : ℝ) : 0 < U L := by unfold U k; positivity

theorem log_U (L : ℝ) : log (U L) = ulog L := by
  rw [U,log_mul (by norm_num [k] : k≠0) (exp_ne_zero _),log_exp]
  unfold ulog
  ring

theorem ulog_pos {L : ℝ} (hL : (330 : ℝ) ≤ L) : 0 < ulog L := by
  have hk : 0 ≤ log k := log_nonneg (by norm_num [k])
  unfold ulog
  linarith

theorem ulog_mono : Monotone ulog := by
  intro x y hxy
  unfold ulog
  linarith

theorem factor4_nonneg {s u : ℝ} (hs : s∈Icc (3/4 : ℝ) (7/8 : ℝ)) (hu : 0<u) :
    0 ≤ factor4 s u := by
  have hb : 0<b s := by unfold b p; linarith [hs.1]
  have h0 : 0≤q s := by unfold q; linarith [hs.2]
  have h1 : 0≤q s-1 := by unfold q; linarith [hs.2]
  have h2 : 0≤q s-2 := by unfold q; linarith [hs.2]
  have h3 : 0≤q s-3 := by unfold q; linarith [hs.2]
  unfold factor4
  positivity

theorem factor4_antitone {s : ℝ} (hs : s∈Icc (3/4 : ℝ) (7/8 : ℝ)) :
    AntitoneOn (factor4 s) (Ioi 0) := by
  intro u hu v hv huv
  change 0<u at hu
  change 0<v at hv
  have hb : 0<b s := by unfold b p; linarith [hs.1]
  have h0 : 0≤q s := by unfold q; linarith [hs.2]
  have h1 : 0≤q s-1 := by unfold q; linarith [hs.2]
  have h2 : 0≤q s-2 := by unfold q; linarith [hs.2]
  have h3 : 0≤q s-3 := by unfold q; linarith [hs.2]
  unfold factor4
  gcongr <;> positivity

theorem factor2_nonneg {u : ℝ} (hu : 0<u) : 0≤factor2 u := by
  unfold factor2
  positivity

theorem factor2_antitone : AntitoneOn factor2 (Ioi 0) := by
  intro u hu v hv huv
  change 0<u at hu
  change 0<v at hv
  unfold factor2
  gcongr <;> positivity

theorem mainRay_antitone {s : ℝ} (hs : s∈Icc (3/4 : ℝ) (7/8 : ℝ)) :
    AntitoneOn (mainRay s) (Ici 330) := by
  have hbase := affine_power_exp_antitone (r:=rate s) (m:=q s) (c:=log k)
    (by unfold rate; linarith [hs.2]) (by unfold q; linarith [hs.1])
    (log_nonneg (by norm_num [k]))
  intro L hL M hM hLM
  have h1 := hbase hL hM hLM
  have h2 := factor4_antitone hs (ulog_pos hL) (ulog_pos hM) (ulog_mono hLM)
  have hb : 0<b s := by unfold b p; linarith [hs.1]
  unfold mainRay
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · exact h2
  · exact factor4_nonneg hs (ulog_pos hM)
  · have hLL : (330 : ℝ)≤L := hL
    have hL0 : 0≤L := by linarith
    have huL : 0<ulog L := ulog_pos hL
    positivity

theorem correctionRay_antitone {s : ℝ} (hs : s∈Icc (3/4 : ℝ) (7/8 : ℝ)) :
    AntitoneOn (correctionRay s) (Ici 330) := by
  have hbase := affine_power_exp_antitone (r:=1-s) (m:=2) (c:=log k)
    (by linarith [hs.2]) (by norm_num) (log_nonneg (by norm_num [k]))
  intro L hL M hM hLM
  have h1 : M*exp (-(1-s)*M)*(ulog M)^2 ≤ L*exp (-(1-s)*L)*(ulog L)^2 := by
    simpa only [Real.rpow_two,ulog] using hbase hL hM hLM
  have h2 := factor2_antitone (ulog_pos hL) (ulog_pos hM) (ulog_mono hLM)
  unfold correctionRay
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  · exact h2
  · exact factor2_nonneg (ulog_pos hM)
  · have hLL : (330 : ℝ)≤L := hL
    have hL0 : 0≤L := by linarith
    have huL : 0<ulog L := ulog_pos hL
    positivity

theorem moment_as_factors (s L : ℝ) :
    moment s (U L) = (9795/1000 : ℝ)*
      ((U L)^(p s-1)*(ulog L)^(q s)/b s*factor4 s (ulog L))+
      (4465/1000 : ℝ)*(((ulog L)^2+2*ulog L+2)/U L) := by
  unfold moment CH2QRH.densityMomentMain
  dsimp only
  rw [log_U]
  rfl

theorem normalized_exp_factor (s L : ℝ) :
    k*exp (L/5)*exp (-(1-s)*L)*(U L)^(p s-1) =
      exp (p s*log k)*exp (-rate s*L) := by
  rw [Real.rpow_def_of_pos (U_pos L),log_U]
  calc
    _ = exp (log k)*exp (L/5)*exp (-(1-s)*L)*exp (ulog L*(p s-1)) := by
      rw [exp_log (by norm_num [k] : 0<k)]
    _ = exp (log k+L/5+ (-(1-s)*L)+ulog L*(p s-1)) := by
      simp only [exp_add]
    _ = _ := by
      rw [←exp_add]
      congr 1
      unfold ulog p rate
      ring

theorem integrand_eq (s L : ℝ) (hs : s∈Icc (3/4 : ℝ) (7/8 : ℝ))
    (hL : (330 : ℝ)≤L) : integrand L s = mainRay s L+correctionRay s L := by
  have hu : ulog L≠0 := (ulog_pos hL).ne'
  have hU : U L≠0 := (U_pos L).ne'
  have hb : b s≠0 := by unfold b p; linarith [hs.1]
  unfold integrand
  rw [moment_as_factors]
  calc
    _ = 2*(9795/1000 : ℝ)*L*
        (k*exp (L/5)*exp (-(1-s)*L)*(U L)^(p s-1))*(ulog L)^(q s)/b s*
          factor4 s (ulog L)+
        2*(4465/1000 : ℝ)*L*exp (-(1-s)*L)*((ulog L)^2+2*ulog L+2) := by
      unfold U
      field_simp
      <;> ring
    _ = _ := by
      rw [normalized_exp_factor]
      unfold mainRay correctionRay factor2
      field_simp
      <;> ring

theorem integrand_antitone {s : ℝ} (hs : s∈Icc (3/4 : ℝ) (7/8 : ℝ)) :
    AntitoneOn (fun L ↦ integrand L s) (Ici 330) := by
  intro L hL M hM hLM
  change integrand M s ≤ integrand L s
  rw [integrand_eq s L hs hL,integrand_eq s M hs hM]
  exact add_le_add (mainRay_antitone hs hL hM hLM) (correctionRay_antitone hs hL hM hLM)

theorem high_as_integral (L : ℝ) :
    high L = ∫ s in (3/4 : ℝ)..(7/8 : ℝ),integrand L s := by
  unfold high integrand
  rw [←intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

theorem integrand_intervalIntegrable {L : ℝ} (hU : 1<U L) :
    IntervalIntegrable (integrand L) volume (3/4 : ℝ) (7/8 : ℝ) := by
  have hc := moment_continuousOn hU
  have he : Continuous (fun s : ℝ ↦ 2*k*L*exp (L/5)*exp (-(1-s)*L)) := by fun_prop
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (3/4 : ℝ)≤7/8)]
  exact he.continuousOn.mul hc

theorem high_antitone : AntitoneOn high (Ici 330) := by
  intro L hL M hM hLM
  have hlogL : 0<log (U L) := by rw [log_U];exact ulog_pos hL
  have hlogM : 0<log (U M) := by rw [log_U];exact ulog_pos hM
  have hUL : 1<U L := (log_pos_iff (U_pos L).le).mp hlogL
  have hUM : 1<U M := (log_pos_iff (U_pos M).le).mp hlogM
  rw [high_as_integral,high_as_integral]
  apply intervalIntegral.integral_mono_on (by norm_num) (integrand_intervalIntegrable hUM)
    (integrand_intervalIntegrable hUL)
  intro s hs
  exact integrand_antitone hs hL hM hLM

end E1FrozenN.Interval
#print axioms E1FrozenN.Interval.mainRay_antitone
#print axioms E1FrozenN.Interval.correctionRay_antitone
#print axioms E1FrozenN.Interval.high_antitone
