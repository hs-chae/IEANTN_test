/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalB.Common

namespace HighAnchorIntervalB
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def rate (s : ℝ) : ℝ := (11/25:ℝ)*(1-s)
noncomputable def mainRay (s L : ℝ) : ℝ :=
  (2*coeff s*exp (p s*log k)/b s)*
    (L*exp (-rate s*L)*(ulog L)^(q s))*DirectIntervalA.factor4 s (ulog L)
noncomputable def correctionRay (s L : ℝ) : ℝ :=
  12*(L*exp (-(1-s)*L)*(ulog L)^2)*DirectIntervalA.factor2 (ulog L)
noncomputable def integrand (L s : ℝ) : ℝ :=
  2*U L*L*exp (-(1-s)*L)*moment s (U L)

theorem U_pos (L : ℝ) : 0 < U L := by unfold U k;positivity
theorem log_U (L : ℝ) : log (U L)=ulog L := by
  rw [U,log_mul (by norm_num [k] : k≠0) (exp_ne_zero _),log_exp]
  unfold ulog
  ring
theorem ulog_pos {L : ℝ} (hL : (330:ℝ)≤L) : 0<ulog L := by
  have hc:=log_nonneg (by norm_num [k] : (1:ℝ)≤k)
  unfold ulog eta
  linarith
theorem ulog_mono : Monotone ulog := by
  intro x y hxy
  unfold ulog eta
  linarith

/-- Each affine-log monomial decreases on the entire real ray. The exponent
may be negative, as occurs in the fourth moment correction. -/
theorem affine_power_exp_antitone {a r m C : ℝ} (ha : 0<a)
    (hr : (1/20:ℝ)≤r) (hm : m≤7/2) (hC : 0≤C) :
    AntitoneOn (fun L:ℝ=>L*exp (-r*L)*(a*L+C)^m) (Ici 330) := by
  let f : ℝ→ℝ := fun L=>L*exp (-r*L)*(a*L+C)^m
  let d : ℝ→ℝ := fun L=>exp (-r*L)*(a*L+C)^m*(1-r*L+L*m*a/(a*L+C))
  have hd : ∀L∈Ici (330:ℝ),HasDerivAt f (d L) L := by
    intro L hL
    have hL0 : 0<L := lt_of_lt_of_le (by norm_num) hL
    have hu : 0<a*L+C := by positivity
    have he:=((hasDerivAt_id L).const_mul (-r)).exp
    have hp:=(((hasDerivAt_id L).const_mul a).add_const C).rpow_const (p:=m) (Or.inl hu.ne')
    convert ((hasDerivAt_id L).mul he).mul hp using 1 <;> first
    | rfl
    | (simp only [id_eq,Pi.mul_apply,f,d]
       rw [Real.rpow_sub_one hu.ne' m]
       field_simp
       <;> ring)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (330:ℝ))
    (fun L hL=>(hd L hL).continuousAt.continuousWithinAt)
    (fun L hL=>(hd L (interior_subset hL)).hasDerivWithinAt)
  intro L hL
  have hLL : (330:ℝ)≤L := interior_subset hL
  have hL0 : 0<L := lt_of_lt_of_le (by norm_num) hLL
  have hu : 0<a*L+C := by positivity
  have hf : L*m*a/(a*L+C)≤7/2 := by
    apply (div_le_iff₀ hu).mpr
    have hh:=mul_le_mul_of_nonneg_left hm (show 0≤a*L by positivity)
    nlinarith
  have hrL : (1/20:ℝ)*330≤r*L := mul_le_mul hr hLL (by norm_num) (by linarith)
  have hsign : 1-r*L+L*m*a/(a*L+C)≤0 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hsign

theorem mainRay_antitone {s : ℝ} (hs : s∈Icc (3/4:ℝ) (7/8:ℝ)) :
    AntitoneOn (mainRay s) (Ici 330) := by
  have hbase:=affine_power_exp_antitone (a:=eta) (r:=rate s) (m:=q s) (C:=log k)
    (by norm_num [eta]) (by unfold rate;linarith [hs.2])
    (by dsimp [q];linarith [hs.1]) (log_nonneg (by norm_num [k]))
  intro L hL M hM hLM
  have h1:=hbase hL hM hLM
  have h2:=DirectIntervalA.factor4_antitone hs (ulog_pos hL) (ulog_pos hM) (ulog_mono hLM)
  have hb : 0<b s := by dsimp [b,p];linarith [hs.1]
  have hc:=coeff_nonneg s
  have hL0 : 0≤L := by have hh:(330:ℝ)≤L:=hL;linarith
  have huL:=ulog_pos hL
  unfold mainRay
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · exact h2
  · exact DirectIntervalA.factor4_nonneg hs (ulog_pos hM)
  · positivity

theorem correctionRay_antitone {s : ℝ} (hs : s∈Icc (3/4:ℝ) (7/8:ℝ)) :
    AntitoneOn (correctionRay s) (Ici 330) := by
  have hbase:=affine_power_exp_antitone (a:=eta) (r:=1-s) (m:=2) (C:=log k)
    (by norm_num [eta]) (by linarith [hs.2]) (by norm_num) (log_nonneg (by norm_num [k]))
  intro L hL M hM hLM
  have h1 : M*exp (-(1-s)*M)*(ulog M)^2≤L*exp (-(1-s)*L)*(ulog L)^2 := by
    simpa only [Real.rpow_two,ulog] using hbase hL hM hLM
  have h2:=DirectIntervalA.factor2_antitone (ulog_pos hL) (ulog_pos hM) (ulog_mono hLM)
  have hL0 : 0≤L := by have hh:(330:ℝ)≤L:=hL;linarith
  have huL:=ulog_pos hL
  unfold correctionRay
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  · exact h2
  · exact DirectIntervalA.factor2_nonneg (ulog_pos hM)
  · positivity

theorem moment_as_factors (s L : ℝ) :
    moment s (U L)=coeff s*((U L)^(p s-1)*(ulog L)^(q s)/b s*
      DirectIntervalA.factor4 s (ulog L))+6*(((ulog L)^2+2*ulog L+2)/U L) := by
  unfold moment CH2QRH.densityMomentMain
  dsimp only
  rw [log_U]
  rfl

theorem normalized_exp_factor (s L : ℝ) :
    k*exp (eta*L)*exp (-(1-s)*L)*(U L)^(p s-1)=
      exp (p s*log k)*exp (-rate s*L) := by
  rw [Real.rpow_def_of_pos (U_pos L),log_U]
  calc
    _ = exp (log k)*exp (eta*L)*exp (-(1-s)*L)*exp (ulog L*(p s-1)) := by
      rw [exp_log (by norm_num [k] : 0<k)]
    _ = exp (log k+eta*L+(-(1-s)*L)+ulog L*(p s-1)) := by simp only [exp_add]
    _ = _ := by rw [←exp_add];congr 1;unfold ulog p rate eta;ring

theorem integrand_eq (s L : ℝ) (hs : s∈Icc (3/4:ℝ) (7/8:ℝ))
    (hL : (330:ℝ)≤L) : integrand L s=mainRay s L+correctionRay s L := by
  have hu:ulog L≠0:=(ulog_pos hL).ne'
  have hU:U L≠0:=(U_pos L).ne'
  have hb:b s≠0:=by dsimp [b,p];linarith [hs.1]
  unfold integrand
  rw [moment_as_factors]
  calc
    _ = 2*coeff s*L*(k*exp (eta*L)*exp (-(1-s)*L)*(U L)^(p s-1))*
        (ulog L)^(q s)/b s*DirectIntervalA.factor4 s (ulog L)+
        12*L*exp (-(1-s)*L)*((ulog L)^2+2*ulog L+2) := by
      unfold U
      field_simp
      <;> ring
    _ = _ := by
      rw [normalized_exp_factor]
      unfold mainRay correctionRay DirectIntervalA.factor2
      field_simp
      <;> ring

theorem integrand_antitone {s : ℝ} (hs : s∈Icc (3/4:ℝ) (7/8:ℝ)) :
    AntitoneOn (fun L=>integrand L s) (Ici 330) := by
  intro L hL M hM hLM
  change integrand M s ≤ integrand L s
  rw [integrand_eq s L hs hL,integrand_eq s M hs hM]
  exact add_le_add (mainRay_antitone hs hL hM hLM) (correctionRay_antitone hs hL hM hLM)

theorem high_as_integral (L : ℝ) : high L=∫s in (3/4:ℝ)..(7/8:ℝ),integrand L s := by
  unfold high integrand
  rw [←intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

theorem integrand_intervalIntegrable {L : ℝ} (hU : 1<U L) :
    IntervalIntegrable (integrand L) volume (3/4:ℝ) (7/8:ℝ) := by
  have hc:=moment_continuousOn hU
  have he:Continuous (fun s:ℝ=>2*U L*L*exp (-(1-s)*L)):=by fun_prop
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (3/4:ℝ)≤7/8)]
  exact he.continuousOn.mul hc

theorem high_antitone : AntitoneOn high (Ici 330) := by
  intro L hL M hM hLM
  have hl:0<log (U L):=by rw [log_U];exact ulog_pos hL
  have hm:0<log (U M):=by rw [log_U];exact ulog_pos hM
  have hUL:1<U L:=(log_pos_iff (U_pos L).le).mp hl
  have hUM:1<U M:=(log_pos_iff (U_pos M).le).mp hm
  rw [high_as_integral,high_as_integral]
  apply intervalIntegral.integral_mono_on (by norm_num) (integrand_intervalIntegrable hUM)
    (integrand_intervalIntegrable hUL)
  intro s hs
  exact integrand_antitone hs hL hM hLM

end HighAnchorIntervalB
#print axioms HighAnchorIntervalB.high_antitone
