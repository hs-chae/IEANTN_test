/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Spectral

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- Reflection across the critical line preserves the ordinate. -/
def zeroReflect (s : ℂ) : ℂ := 1 - (starRingEnd ℂ) s

/-- The zeta functional equation preserves zero multiplicity away from the real axis. -/
theorem zetaOrder_one_sub {s : ℂ} (hsim : s.im ≠ 0) :
    IEANTN.zetaOrder (1 - s) = IEANTN.zetaOrder s := by
  have hnat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    exact hsim (by simpa [hn])
  have hs1 : s ≠ 1 := by intro h; exact hsim (by simp [h])
  have hopen : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hloc : (fun z : ℂ ↦ riemannZeta (1 - z)) =ᶠ[𝓝 s]
      (fun z ↦ 2 * (2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z *
        Complex.cos (Real.pi * z / 2) * riemannZeta z) := by
    filter_upwards [hopen.mem_nhds hsim] with z hz
    exact riemannZeta_one_sub
      (fun n hn ↦ hz (by simp [hn])) (fun he ↦ hz (by simp [he]))
  have hGamma : AnalyticAt ℂ Complex.Gamma s := by
    have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | z.im ≠ 0} := by
      intro z hz
      exact (Complex.differentiableAt_Gamma z
        (fun n hn ↦ hz (by simp [hn]))).differentiableWithinAt
    exact hd.analyticOnNhd hopen s hsim
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have hpow : AnalyticAt ℂ (fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    (differentiable_id.neg.const_cpow (Or.inl h2pi)).analyticAt s
  have hpow0 : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero
      (by intro h; exact hsim (by simpa using congrArg Complex.im h))).mpr h2pi
  have hcos0 : Complex.cos (Real.pi * s / 2) ≠ 0 := by
    intro hz
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hz
    have hi : Real.pi * s.im / 2 = 0 := by simpa using congrArg Complex.im hk
    exact hsim (by have hp := Real.pi_pos; nlinarith)
  have hA : AnalyticAt ℂ (fun z : ℂ ↦
      2 * (2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z *
        Complex.cos (Real.pi * z / 2)) s := by
    exact ((analyticAt_const.mul hpow).mul hGamma).mul (by fun_prop)
  have hA0 : 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
      Complex.cos (Real.pi * s / 2) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpow0)
      (Complex.Gamma_ne_zero hnat)) hcos0
  have hcomp : meromorphicOrderAt (fun z : ℂ ↦ riemannZeta (1 - z)) s =
      meromorphicOrderAt riemannZeta (1 - s) := by
    have hd : deriv (fun z : ℂ ↦ 1 - z) s ≠ 0 := by
      rw [deriv_const_sub, deriv_id'']; norm_num
    exact meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) hd
  have hmul := meromorphicOrderAt_mul_of_ne_zero (f := riemannZeta) hA hA0
  change meromorphicOrderAt (fun z : ℂ ↦
    (2 * (2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z * Complex.cos (Real.pi * z / 2)) *
      riemannZeta z) s = meromorphicOrderAt riemannZeta s at hmul
  have he := hcomp.symm.trans
    ((meromorphicOrderAt_congr (hloc.filter_mono nhdsWithin_le_nhds)).trans hmul)
  exact congrArg (fun o : WithTop ℤ ↦ o.untopD 0) he

/-- The reflection is an involution, so no zeros or multiplicities are lost. -/
theorem zeroReflect_involutive : Function.Involutive zeroReflect := by
  intro s
  simp [zeroReflect]

/-- Reflection preserves the positive-ordinate zero set. -/
theorem zeroReflect_mem {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc 0 t)) :
    zeroReflect ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc 0 t) := by
  have hi : ρ.im ≠ 0 := hρ.2.1.1.ne'
  have hconj : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
    rw [riemannZeta_conj, hρ.2.2, map_zero]
  have hnat : ∀ n : ℕ, (starRingEnd ℂ) ρ ≠ -(n : ℂ) := by
    intro n hn
    have hh := congrArg Complex.im hn
    simp only [Complex.conj_im, Complex.neg_im, Complex.natCast_im, neg_zero] at hh
    exact hi (neg_eq_zero.mp hh)
  have h1 : (starRingEnd ℂ) ρ ≠ 1 := by
    intro hn
    have hh := congrArg Complex.im hn
    simp at hh
    exact hi hh
  refine ⟨trivial, ?_, ?_⟩
  · simpa [zeroReflect] using hρ.2.1
  · change riemannZeta (1 - (starRingEnd ℂ) ρ) = 0
    rw [riemannZeta_one_sub hnat h1, hconj, mul_zero]

/-- Reflection preserves zero multiplicity. -/
theorem zetaOrder_zeroReflect {ρ : ℂ} (hi : ρ.im ≠ 0) :
    IEANTN.zetaOrder (zeroReflect ρ) = IEANTN.zetaOrder ρ := by
  rw [zeroReflect, zetaOrder_one_sub (by simpa using hi)]
  exact CH2Section6.zetaOrder_conj ρ

/-- Reindex a finite CH2 zero sum by critical-line reflection. -/
theorem zsum_zeroReflect {t : ℝ} (f : ℂ → ℝ) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) (fun ρ ↦ f (zeroReflect ρ)) =
      IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) f := by
  classical
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := t) le_rfl
  rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin, CH2Section7Z.zetaZeroesSum_eq_sum hfin]
  apply Finset.sum_bij (fun ρ _ ↦ zeroReflect ρ)
  · intro ρ hρ
    exact (Set.Finite.mem_toFinset hfin).mpr
      (zeroReflect_mem ((Set.Finite.mem_toFinset hfin).mp hρ))
  · intro ρ hρ σ hσ he
    exact zeroReflect_involutive.injective he
  · intro ρ hρ
    refine ⟨zeroReflect ρ, ?_, zeroReflect_involutive ρ⟩
    exact (Set.Finite.mem_toFinset hfin).mpr
      (zeroReflect_mem ((Set.Finite.mem_toFinset hfin).mp hρ))
  · intro ρ hρ
    have hi := ((Set.Finite.mem_toFinset hfin).mp hρ).2.1.1.ne'
    rw [zetaOrder_zeroReflect hi]

end CH2QRH
