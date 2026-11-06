/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.GaussianQuadrature

namespace PVEvolutionA.Recovery.Gaussian
open Real Set MeasureTheory
set_option maxHeartbeats 0

def basisN : Fin 12→ℕ := ![8,2,7,1,6,0,8,2,8,2,7,1]
def basisK : Fin 12→ℕ := ![0,0,0,0,0,0,1,1,2,2,1,1]

noncomputable def coefficient (m1 m2 h r0 r1 ε sign : ℝ) : Fin 12→ℝ := ![
  (1+ε)*m1,
  (1+ε)*m2,
  (1+ε)*2*r0*m1,
  (1+ε)*2*r0*m2,
  (1+ε)*r0^2*m1+(1+1/ε)*r1^2,
  (1+ε)*r0^2*m2,
  (1+ε)*(2*sign/h)*m1,
  (1+ε)*(2*sign/h)*m2,
  (1+ε)*(sign^2/h^2)*m1,
  (1+ε)*(sign^2/h^2)*m2,
  (1+ε)*(2*r0*sign/h)*m1,
  (1+ε)*(2*r0*sign/h)*m2]

theorem young_eq_sum (m1 m2 h r0 r1 ε sign y : ℝ) :
    young m1 m2 h r0 r1 ε sign y =
      ∑ i : Fin 12, coefficient m1 m2 h r0 r1 ε sign i * basis (basisN i) (basisK i) y := by
  rw [young_eq_reduced]
  norm_num [reduced,coefficient,basisN,basisK,Fin.sum_univ_succ]
  ring

theorem coefficient_nonneg {m1 m2 h r0 r1 ε sign : ℝ}
    (hm1 : 0≤m1) (hm2 : 0≤m2) (hh : 0<h) (hr0 : 0≤r0) (hε : 0<ε)
    (hs : 0≤sign) (i : Fin 12) : 0≤coefficient m1 m2 h r0 r1 ε sign i := by
  fin_cases i <;> norm_num [coefficient] <;> positivity

theorem coefficient_zero (m1 m2 h r0 r1 ε : ℝ) (i : Fin 12) :
    coefficient m1 m2 h r0 r1 ε 0 i =
      if i.val<6 then coefficient m1 m2 h r0 r1 ε 1 i else 0 := by
  fin_cases i <;> norm_num [coefficient]

theorem young_continuous (m1 m2 h r0 r1 ε sign : ℝ) :
    Continuous (young m1 m2 h r0 r1 ε sign) := by
  unfold young weight
  fun_prop

theorem integral_young (m1 m2 h r0 r1 ε sign a b : ℝ) :
    (∫y in a..b,young m1 m2 h r0 r1 ε sign y) =
      ∑ i : Fin 12, coefficient m1 m2 h r0 r1 ε sign i *
        (∫y in a..b,basis (basisN i) (basisK i) y) := by
  simp_rw [young_eq_sum]
  rw [intervalIntegral.integral_finset_sum]
  · simp only [intervalIntegral.integral_const_mul]
  · intro i hi
    exact ((basis_continuous (basisN i) (basisK i)).intervalIntegrable a b).const_mul _

noncomputable def basisIntegral (i : Fin 12) : ℝ :=
  (∫y in (0:ℝ)..3,basis (basisN i) (basisK i) y)+
    if i.val<6 then (∫y in (-20:ℝ)..0,basis (basisN i) (basisK i) y) else 0

/-- The signed square-root kernel on the entire finite interval is controlled
by twelve positive basis integrals. Every coefficient direction is explicit. -/
theorem finite_integral_le_basis {m1 m2 h r0 r1 ε : ℝ}
    (hm1 : 0≤m1) (hm2 : 0≤m2) (hε : 0<ε) :
    (∫y in (-20:ℝ)..3,WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1 y) ≤
      ∑ i : Fin 12, coefficient m1 m2 h r0 r1 ε 1 i * basisIntegral i := by
  have hk : Continuous (WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1) := by
    unfold WinnerBetaA.SignedHeight.kernel
    fun_prop
  have hn : (∫y in (-20:ℝ)..0,WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1 y) ≤
      ∫y in (-20:ℝ)..0,young m1 m2 h r0 r1 ε 0 y := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hk.intervalIntegrable _ _)
      ((young_continuous _ _ _ _ _ _ _).intervalIntegrable _ _)
    intro y hy
    have hp := kernel_le_young m1 m2 h r0 r1 ε y hm1 hm2 hε
    simpa only [if_pos hy.2] using hp
  have hp : (∫y in (0:ℝ)..3,WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1 y) ≤
      ∫y in (0:ℝ)..3,young m1 m2 h r0 r1 ε 1 y := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hk.intervalIntegrable _ _)
      ((young_continuous _ _ _ _ _ _ _).intervalIntegrable _ _)
    intro y hy
    by_cases hz : y≤0
    · have he : y=0 := le_antisymm hz hy.1
      subst y
      have hp := kernel_le_young m1 m2 h r0 r1 ε 0 hm1 hm2 hε
      simpa [young] using hp
    · simpa only [if_neg hz] using kernel_le_young m1 m2 h r0 r1 ε y hm1 hm2 hε
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hk.intervalIntegrable (μ:=volume) (-20) 0) (hk.intervalIntegrable (μ:=volume) 0 3)
  rw [integral_young] at hn hp
  have hc : (∑i : Fin 12, coefficient m1 m2 h r0 r1 ε 0 i *
      (∫y in (-20:ℝ)..0,basis (basisN i) (basisK i) y))+
      (∑i : Fin 12, coefficient m1 m2 h r0 r1 ε 1 i *
      (∫y in (0:ℝ)..3,basis (basisN i) (basisK i) y)) =
      ∑i : Fin 12, coefficient m1 m2 h r0 r1 ε 1 i*basisIntegral i := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [coefficient_zero]
    unfold basisIntegral
    split_ifs <;> ring
  linarith

theorem finite_integral_le_caps {m1 m2 h r0 r1 ε : ℝ} (caps : Fin 12→ℝ)
    (hm1 : 0≤m1) (hm2 : 0≤m2) (hh : 0<h) (hr0 : 0≤r0) (hε : 0<ε)
    (hcaps : ∀i,basisIntegral i≤caps i) :
    (∫y in (-20:ℝ)..3,WinnerBetaA.SignedHeight.kernel m1 m2 h r0 r1 y) ≤
      ∑ i : Fin 12, coefficient m1 m2 h r0 r1 ε 1 i*caps i := by
  apply (finite_integral_le_basis hm1 hm2 hε).trans
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hcaps i)
    (coefficient_nonneg hm1 hm2 hh hr0 hε (by norm_num) i)

#print axioms finite_integral_le_caps
end PVEvolutionA.Recovery.Gaussian
