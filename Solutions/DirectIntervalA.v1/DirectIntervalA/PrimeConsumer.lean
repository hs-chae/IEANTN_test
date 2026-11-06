/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.LogDomain
import IEANTN.Vocabulary.PrimeGaps

namespace DirectIntervalA
open Real Set MeasureTheory Complex
set_option maxHeartbeats 0

/-- The prime-existence half of the existing PrimeInterval characterization,
restated under a unique module name so no ambiguous `Solution` is imported. -/
theorem theta_increase_has_prime {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h)
    (hθ : Chebyshev.theta x < Chebyshev.theta (x+h)) :
    IEANTN.HasPrimeInInterval x h := by
  classical
  let s : Finset ℕ := (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime
  let t : Finset ℕ := (Finset.Icc 0 ⌊x+h⌋₊).filter Nat.Prime
  have hs : s ⊆ t := by
    intro p hp
    obtain ⟨hI,hp⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hI).1,(Finset.mem_Icc.mp hI).2.trans
        (Nat.floor_mono (by linarith : x ≤ x+h))⟩,hp⟩
  have hsum : (∑ p ∈ s, Real.log p) < ∑ p ∈ t, Real.log p := by
    simpa [Chebyshev.theta_eq_sum_Icc,s,t] using hθ
  have hne : s ≠ t := by intro he;rw [he] at hsum;exact (lt_irrefl _ hsum)
  obtain ⟨p,hpt,hps⟩ := Finset.exists_of_ssubset (hs.ssubset_of_ne hne)
  obtain ⟨hpI,hprime⟩ := Finset.mem_filter.mp hpt
  have hpx : ⌊x⌋₊ < p := by
    by_contra hn
    exact hps (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.zero_le p,not_lt.mp hn⟩,hprime⟩)
  refine ⟨p,hprime,?_,?_⟩
  · calc x < (⌊x⌋₊ : ℝ)+1 := Nat.lt_floor_add_one x
         _ ≤ p := by exact_mod_cast hpx
  · calc (p:ℝ) ≤ (⌊x+h⌋₊:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hpI).2
         _ ≤ x+h := Nat.floor_le (by linarith)

/-- A generic actual psi increment and prime-power allowance imply a prime. -/
theorem hasPrime_of_psi_increment {x h E P : ℝ} (hx : 1 ≤ x) (hh : 0 < h)
    (hpsi : (1-E)*h ≤ Chebyshev.psi (x+h)-Chebyshev.psi x)
    (hpp : Chebyshev.psi (x+h)-Chebyshev.theta (x+h) ≤ P*h)
    (hmargin : E+P < 1) : IEANTN.HasPrimeInInterval x h := by
  apply theta_increase_has_prime (by linarith) hh.le
  have hxθ := Chebyshev.theta_le_psi x
  nlinarith

theorem exp_gap_le_exp {L : ℝ} (hL : 330 ≤ L) :
    Real.exp (4*L/5) ≤ Real.exp L := by
  exact Real.exp_le_exp.mpr (by linarith)

theorem exp_endpoint_upper {L : ℝ} (hL : 330 ≤ L) :
    Real.exp L+Real.exp (4*L/5) ≤ Real.exp (L+1) := by
  rw [Real.exp_add]
  have hh := exp_gap_le_exp hL
  have he := Real.exp_one_gt_two
  nlinarith [Real.exp_pos L]

theorem exp_endpoint_log_upper {L : ℝ} (hL : 330 ≤ L) :
    Real.log (Real.exp L+Real.exp (4*L/5)) ≤ L+1 := by
  have hh := Real.log_le_log (show 0<Real.exp L+Real.exp (4*L/5) by positivity)
    (exp_endpoint_upper hL)
  simpa only [Real.log_exp] using hh

/-- Uniform CHJ-II truncation loss on the complete real logarithmic ray. -/
theorem truncation_error_bound {L : ℝ} (hL : 330 ≤ L) :
    (2894/1000:ℝ)*((Real.exp L+Real.exp (4*L/5))*
      Real.log (Real.exp L+Real.exp (4*L/5))+Real.exp L*L)/truncHeight L ≤
      (49/1000:ℝ)*Real.exp (4*L/5) := by
  have hT : 0 < truncHeight L := by unfold truncHeight;positivity
  have hL1 : 0 ≤ L+1 := by linarith
  have hratio : Real.exp (4*L/5) ≤ (1/100:ℝ)*Real.exp L := by
    have hd := delta_le_hundredth hL
    rw [←gap_ratio L] at hd
    exact (div_le_iff₀ (Real.exp_pos L)).mp hd
  have hy : Real.exp L+Real.exp (4*L/5) ≤ (101/100:ℝ)*Real.exp L := by linarith
  have hlog := exp_endpoint_log_upper hL
  have hlog0 : 0 ≤ Real.log (Real.exp L+Real.exp (4*L/5)) := by
    apply Real.log_nonneg
    linarith [Real.add_one_le_exp L,Real.exp_pos (4*L/5)]
  have hnum : (2894/1000:ℝ)*((Real.exp L+Real.exp (4*L/5))*
      Real.log (Real.exp L+Real.exp (4*L/5))+Real.exp L*L) ≤
      (2894/1000:ℝ)*((101/100:ℝ)*Real.exp L*(L+1)+Real.exp L*L) := by
    gcongr
  have hcoef : (2894/1000:ℝ)*((201/100:ℝ)*L+101/100) ≤
      (49/1000:ℝ)*120*L := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hcoef (Real.exp_pos L).le
  have he : Real.exp (4*L/5)*Real.exp (L/5)=Real.exp L := by
    rw [←Real.exp_add];congr 1;ring
  apply (div_le_iff₀ hT).mpr
  apply hnum.trans
  have halg : (49/1000:ℝ)*Real.exp (4*L/5)*truncHeight L =
      Real.exp L*((49/1000:ℝ)*120*L) := by
    unfold truncHeight
    calc _ = ((49/1000:ℝ)*120*L)*(Real.exp (4*L/5)*Real.exp (L/5)) := by ring
         _ = _ := by rw [he];ring
  rw [halg]
  nlinarith only [hscaled]

theorem exp_three_tenths_very_large {L : ℝ} (hL : 330 ≤ L) :
    6000*(L+1) ≤ Real.exp (3*L/10) := by
  have hc : (330:ℝ)^3 ≤ L^3 := by gcongr
  have hq := mul_le_mul_of_nonneg_right hc (show 0≤L by linarith)
  have he := Real.pow_div_factorial_le_exp (3*L/10) (show 0≤3*L/10 by linarith) 4
  norm_num at he hc hq
  nlinarith

/-- Existing Mathlib prime-power control is negligible on this ray. -/
theorem prime_power_error_bound {L : ℝ} (hL : 330 ≤ L) :
    Chebyshev.psi (Real.exp L+Real.exp (4*L/5))-
      Chebyshev.theta (Real.exp L+Real.exp (4*L/5)) ≤
        (1/1000:ℝ)*Real.exp (4*L/5) := by
  have hy1 : 1 ≤ Real.exp L+Real.exp (4*L/5) := by
    have he := Real.add_one_le_exp L
    linarith [Real.exp_pos (4*L/5)]
  have hpp := Chebyshev.psi_sub_theta_le hy1
  have hlog := exp_endpoint_log_upper hL
  have hlog0 : 0 ≤ Real.log (Real.exp L+Real.exp (4*L/5)) := Real.log_nonneg hy1
  have hsqrt := Real.sqrt_le_sqrt (exp_endpoint_upper hL)
  rw [←Real.exp_half] at hsqrt
  have hhalf : Real.exp (1/2:ℝ) ≤ 3 :=
    (Real.exp_le_exp.mpr (by norm_num : (1/2:ℝ)≤1)).trans Real.exp_one_lt_three.le
  have hehalf : Real.exp ((L+1)/2) ≤ 3*Real.exp (L/2) := by
    rw [show (L+1)/2=L/2+1/2 by ring,Real.exp_add]
    exact mul_le_mul_of_nonneg_left hhalf (Real.exp_pos _).le |>.trans_eq (by ring)
  have hbound : 2*Real.sqrt (Real.exp L+Real.exp (4*L/5))*
      Real.log (Real.exp L+Real.exp (4*L/5)) ≤ 6*Real.exp (L/2)*(L+1) := by
    have hsq : Real.sqrt (Real.exp L+Real.exp (4*L/5)) ≤ 3*Real.exp (L/2) := hsqrt.trans hehalf
    calc _ ≤ 2*(3*Real.exp (L/2))*(L+1) := by gcongr
         _ = _ := by ring
  have hbig := exp_three_tenths_very_large hL
  have hm := mul_le_mul_of_nonneg_left hbig (Real.exp_pos (L/2)).le
  have he : Real.exp (L/2)*Real.exp (3*L/10)=Real.exp (4*L/5) := by
    rw [←Real.exp_add];congr 1;ring
  rw [he] at hm
  apply hpp.trans
  apply hbound.trans
  nlinarith only [hm]

theorem hasPrime_exp_of_psi_error {L E : ℝ} (hL : 330 ≤ L)
    (herror : |Chebyshev.psi (Real.exp L+Real.exp (4*L/5))-
      Chebyshev.psi (Real.exp L)-Real.exp (4*L/5)| ≤ E*Real.exp (4*L/5))
    (hmargin : E+1/1000 < 1) :
    IEANTN.HasPrimeInInterval (Real.exp L) (Real.exp (4*L/5)) := by
  apply hasPrime_of_psi_increment (E:=E) (P:=1/1000)
    (by linarith [Real.add_one_le_exp L]) (Real.exp_pos _) _
    (prime_power_error_bound hL) hmargin
  have hh := (abs_le.mp herror).1
  linarith

theorem exp_gap_eq_rpow (L : ℝ) : Real.exp (4*L/5)=(Real.exp L)^(4/5:ℝ) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  congr 1
  ring

theorem real_ray_of_log_ray
    (h : ∀ L : ℝ, 330 ≤ L →
      IEANTN.HasPrimeInInterval (Real.exp L) (Real.exp (4*L/5))) :
    ∀ x : ℝ, Real.exp 330 ≤ x → IEANTN.HasPrimeInInterval x (x^(4/5:ℝ)) := by
  intro x hx
  have hx0 : 0 < x := (Real.exp_pos 330).trans_le hx
  have hlog : 330 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos 330) hx
    simpa only [Real.log_exp] using hh
  have hh := h (Real.log x) hlog
  rw [exp_gap_eq_rpow,Real.exp_log hx0] at hh
  exact hh

#print axioms truncation_error_bound
#print axioms prime_power_error_bound
#print axioms hasPrime_exp_of_psi_error
end DirectIntervalA
