/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.Interval.ComplexIncrement

namespace E1FrozenN.Interval
open Real Set MeasureTheory Complex WinnerDirectKernel
set_option maxHeartbeats 0

/-- Actual positive-ordinate zeros, their multiplicities, and the minimum weight.
This is a finite mathematical sum, rather than a new assumed density bound. -/
noncomputable def positiveZeroBudget (x h T : ℝ) : ℝ :=
  2 * ∑ rho ∈ positiveZeros T, (IEANTN.zetaOrder rho : ℝ) *
    x^rho.re * min (h/x) ((2+h/x)/rho.im)

/-- The existing finite conjugation bijection works for any actual zero weight. -/
theorem signed_sum_eq_paired_generic
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8)) (T : ℝ) (f : ℂ → ℂ) :
    IEANTN.zetaZeroesSum (Ioo 0 1) (Icc (-T) T) f =
      ∑ q ∈ pairedZeros T, f (pairZ q) * (pairW q : ℂ) := by
  classical
  rw [signed_sum_complex]
  symm
  apply Finset.sum_bij (fun q _ => pairZ q)
  · intro q hq
    exact (Set.Finite.mem_toFinset _).mpr (pair_mem_signed hqrh hq)
  · intro q hq r hr he
    exact pair_injective hq hr he
  · intro rho hr
    obtain ⟨q,hq,he⟩ := signed_has_pair ((Set.Finite.mem_toFinset _).mp hr)
    exact ⟨q,hq,he⟩
  · intro q hq
    have hm : (IEANTN.zetaOrder (pairZ q) : ℝ) = pairW q := by
      rcases q with ⟨rho,b⟩
      cases b <;> simp [pairZ,pairW,CH2Section6.zetaOrder_conj]
    have hmC : (IEANTN.zetaOrder (pairZ q) : ℂ) = (pairW q : ℂ) := by
      exact_mod_cast hm
    rw [hmC]

theorem zeroIncrement_conj {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (rho : ℂ) :
    zeroIncrement x h ((starRingEnd ℂ) rho) =
      (starRingEnd ℂ) (zeroIncrement x h rho) := by
  have hy : 0 < x+h := by linarith
  have hargx : (x:ℂ).arg ≠ Real.pi := by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  have hargy : ((x+h:ℝ):ℂ).arg ≠ Real.pi := by rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm
  unfold zeroIncrement
  rw [Complex.cpow_conj _ _ hargy, Complex.cpow_conj _ _ hargx]
  simp only [Complex.conj_ofReal, map_div₀, map_sub]

/-- Conjugate symmetry and nonnegative multiplicity turn the actual signed sum
into twice the positive-ordinate norm sum. -/
theorem norm_signed_increment_le_positive
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (T : ℝ) :
    ‖IEANTN.zetaZeroesSum (Ioo 0 1) (Icc (-T) T) (zeroIncrement x h)‖ ≤
      2 * ∑ rho ∈ positiveZeros T,
        (IEANTN.zetaOrder rho : ℝ) * ‖zeroIncrement x h rho‖ := by
  classical
  rw [signed_sum_eq_paired_generic hqrh]
  have hnorm := norm_sum_le (s := pairedZeros T)
    (f := fun q => zeroIncrement x h (pairZ q) * (pairW q : ℂ))
  apply hnorm.trans_eq
  unfold pairedZeros
  rw [Finset.product_eq_sprod, Finset.sum_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hr
  have hm := positive_mem hr
  have hw := CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hm
  have hc : ‖(IEANTN.zetaOrder rho : ℂ)‖ = (IEANTN.zetaOrder rho : ℝ) := by
    rw [Complex.norm_intCast]
    exact_mod_cast abs_of_nonneg hw
  simp only [Finset.sum_insert, Finset.mem_singleton, Bool.false_eq_true,
    not_false_eq_true, Finset.sum_singleton, pairZ, pairW, ite_false, ite_true,
    norm_mul]
  rw [zeroIncrement_conj hx hh, Complex.norm_conj]
  have hc' : ‖((IEANTN.zetaOrder rho : ℝ) : ℂ)‖ = (IEANTN.zetaOrder rho : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  rw [hc']
  ring

/-- The minimum-weight budget controls the original paper's full signed sum. -/
theorem norm_signed_increment_le_budget
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (T : ℝ) :
    ‖IEANTN.zetaZeroesSum (Ioo 0 1) (Icc (-T) T) (zeroIncrement x h)‖ ≤
      positiveZeroBudget x h T := by
  apply (norm_signed_increment_le_positive hqrh hx hh T).trans
  unfold positiveZeroBudget
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro rho hr
  have hm := positive_mem hr
  have hw := CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hm
  have hre := CH2QRH.re_le_boundary hqrh hm.2.2 hm.2.1.1
  have hi := norm_zeroIncrement_le_min hx hh hm.2.1.1 (by linarith : rho.re ≤ 1)
  convert mul_le_mul_of_nonneg_left hi hw using 1 <;> ring

/-- The exact new literature premise gives an actual psi difference bound with
one common truncation height and the proved finite minimum-weight budget. -/
theorem chjii_to_positive_budget
    (hsource : CHJII_Theorem1_3_Row40)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x h T : ℝ} (hx : Real.exp 40 ≤ x) (hh : 0 ≤ h)
    (hT : max 51 (Real.log x ^ 2) < T) (hupper : T < (Real.sqrt x-2)/4) :
    ∃ Tstar : ℝ, T ≤ Tstar ∧ Tstar ≤ 2*T ∧
      |Chebyshev.psi (x+h)-Chebyshev.psi x-h| ≤
        positiveZeroBudget x h Tstar + (2894/1000 : ℝ)*
          ((x+h)*Real.log (x+h)+x*Real.log x)/T := by
  obtain ⟨Tstar,hlo,hhi,herr⟩ := hsource x h T hx hh hT hupper
  refine ⟨Tstar,hlo,hhi,?_⟩
  have hx0 : 0 < x := (Real.exp_pos 40).trans_le hx
  have hs := norm_signed_increment_le_budget hqrh hx0 hh Tstar
  let Z := IEANTN.zetaZeroesSum (Ioo 0 1) (Icc (-Tstar) Tstar) (zeroIncrement x h)
  have hre : |Z.re| ≤ positiveZeroBudget x h Tstar :=
    (Complex.abs_re_le_norm Z).trans hs
  change |Chebyshev.psi (x+h)-Chebyshev.psi x-h+Z.re| ≤ _ at herr
  rcases abs_le.mp herr with ⟨herrlo,herrhi⟩
  rcases abs_le.mp hre with ⟨hzlo,hzhi⟩
  apply abs_le.mpr
  constructor <;> linarith

#print axioms chjii_to_positive_budget
end E1FrozenN.Interval
