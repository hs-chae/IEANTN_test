/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib
import IEANTN.Nodes.BoxMellinInputs.v1.Conclusions

/-! The actual first Stieltjes sequence converges, and its convex-trapezoid
correction at128 is a rigorous lower bound. No zeta identity or numerical
computation is assumed. This is ordinary kernel mathematics, not source-first PV. -/
namespace RHLimit.Stieltjes
open Real Set MeasureTheory Filter Finset
open scoped Topology
set_option maxHeartbeats 0
noncomputable def f (x : ℝ) : ℝ := Real.log x / x
noncomputable def fp (x : ℝ) : ℝ := (1 - Real.log x) / x ^ 2

lemma hasDerivAt_f {x : ℝ} (hx : x ≠ 0) : HasDerivAt f (fp x) x := by
  have h := (Real.hasDerivAt_log hx).div (hasDerivAt_id x) hx
  apply h.congr_deriv
  dsimp [fp]
  field_simp [hx]

lemma hasDerivAt_fp {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt fp ((2 * Real.log x - 3) / x ^ 3) x := by
  have h := ((hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_log hx)).div
    ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)
  apply h.congr_deriv
  dsimp
  norm_num
  field_simp [hx]
  ring

lemma log_lower {x : ℝ} (hx : 128 ≤ x) : 3 / 2 ≤ Real.log x := by
  have hp : Real.log ((2 : ℝ)^7) = 7 * Real.log 2 := Real.log_pow 2 7
  have h128 : (3 / 2 : ℝ) ≤ Real.log 128 := by
    norm_num at hp
    linarith [Real.log_two_gt_d9]
  exact h128.trans (Real.log_le_log (by norm_num) hx)

lemma f_continuous : ContinuousOn f (Ici 128) := by
  intro x hx
  exact (hasDerivAt_f (by have h : 128 ≤ x := hx; linarith : x ≠ 0)).continuousAt.continuousWithinAt

lemma f_antitone : AntitoneOn f (Ici 128) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 128) f_continuous
  · intro x hx
    apply (hasDerivAt_f (by have h := interior_subset hx; simp at h; linarith)).hasDerivWithinAt
  · intro x hx
    have h : 128 ≤ x := interior_subset hx
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [log_lower h]) (sq_nonneg x)

lemma f_convex : ConvexOn ℝ (Ici 128) f := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fp)
    (f'' := fun x => (2 * Real.log x - 3) / x ^ 3) (convex_Ici 128) f_continuous
  · intro x hx
    exact (hasDerivAt_f (by have h := interior_subset hx; simp at h; linarith)).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_fp (by have h := interior_subset hx; simp at h; linarith)).hasDerivWithinAt
  · intro x hx
    have h : 128 ≤ x := interior_subset hx
    exact div_nonneg (by linarith [log_lower h])
      (pow_nonneg (by linarith : 0 ≤ x) 3)

lemma f_nonneg {x : ℝ} (hx : 128 ≤ x) : 0 ≤ f x :=
  div_nonneg (by linarith [log_lower hx]) (by linarith)

lemma f_integrable {a b : ℝ} (ha : 128 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable f volume a b := by
  apply (f_continuous.mono ?_).intervalIntegrable
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact le_trans ha hx.1

lemma f_integral {a b : ℝ} (ha : 128 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, f x) = (Real.log b)^2 / 2 - (Real.log a)^2 / 2 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (f_integrable ha hab)
  intro x hx
  rw [uIcc_of_le hab] at hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  apply (((Real.hasDerivAt_log hx0).pow 2).div_const 2).congr_deriv
  dsimp [f]
  norm_num
  field_simp [hx0]

lemma trap_integral {a : ℝ} (ha : 128 ≤ a) :
    (∫ x in a..a+1, f x) ≤ (f a + f (a+1)) / 2 := by
  have hab : a ≤ a+1 := by linarith
  have hinter : IntervalIntegrable
      (fun x : ℝ => (a+1-x)*f a + (x-a)*f (a+1)) volume a (a+1) := by
    exact (by fun_prop : Continuous (fun x : ℝ =>
      (a+1-x)*f a + (x-a)*f (a+1))).intervalIntegrable _ _
  have hi : (∫ x in a..a+1, f x) ≤
      ∫ x in a..a+1, (a+1-x)*f a + (x-a)*f (a+1) := by
    apply intervalIntegral.integral_mono_on hab (f_integrable ha hab) hinter
    intro x hx
    have h := f_convex.2 (show a ∈ Ici (128:ℝ) by exact ha)
      (show a+1 ∈ Ici (128:ℝ) from (by linarith : 128 ≤ a+1)) (show 0 ≤ a+1-x by linarith [hx.2])
      (show 0 ≤ x-a by linarith [hx.1]) (show a+1-x+(x-a)=1 by ring)
    simp only [smul_eq_mul] at h
    convert h using 1
    congr 1
    ring
  have hline : (∫ x in a..a+1, (a+1-x)*f a + (x-a)*f (a+1)) =
      (f a + f (a+1))/2 := by
    have hf : ∀ x : ℝ, (a+1-x)*f a+(x-a)*f (a+1) =
        ((a+1)*f a-a*f (a+1))+(f (a+1)-f a)*x := by intro x; ring
    simp_rw [hf]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id]
    · ring
    · exact intervalIntegrable_const
    · exact (by fun_prop : Continuous (fun x : ℝ => (f (a+1)-f a)*x)).intervalIntegrable _ _
  linarith

lemma stieltjes_succ (n : ℕ) (hn : 128 ≤ n) :
    BoxMellinInputs.v1.stieltjesSeq (n+1) - BoxMellinInputs.v1.stieltjesSeq n =
      f ((n:ℝ)+1) - ∫ x in (n:ℝ)..(n:ℝ)+1, f x := by
  rw [f_integral (by exact_mod_cast hn) (by linarith)]
  unfold BoxMellinInputs.v1.stieltjesSeq
  rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n+1)]
  simp only [Nat.cast_add, Nat.cast_one]
  unfold f
  ring

lemma f_right_integral {a : ℝ} (ha : 128 ≤ a) :
    f (a+1) ≤ ∫ x in a..a+1, f x := by
  calc
    _ = ∫ x in a..a+1, f (a+1) := by simp
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on (by linarith)
        intervalIntegrable_const (f_integrable ha (by linarith))
      intro x hx
      apply f_antitone
      · exact le_trans ha hx.1
      · exact show 128 ≤ a+1 from by linarith
      · exact hx.2

lemma stieltjes_antitone :
    Antitone (fun n : ℕ => BoxMellinInputs.v1.stieltjesSeq (n+128)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hs := stieltjes_succ (n+128) (by omega)
  have hr := f_right_integral (a:=((n+128:ℕ):ℝ)) (by exact_mod_cast (show 128 ≤ n+128 by omega))
  have hn : n+1+128 = (n+128)+1 := by omega
  rw [hn]
  linarith

lemma corrected_monotone : Monotone (fun n : ℕ =>
    BoxMellinInputs.v1.stieltjesSeq (n+128) - f (n+128) / 2) := by
  apply monotone_nat_of_le_succ
  intro n
  have hs := stieltjes_succ (n+128) (by omega)
  have ht := trap_integral (a:=((n+128:ℕ):ℝ)) (by exact_mod_cast (show 128 ≤ n+128 by omega))
  have hn : n+1+128 = (n+128)+1 := by omega
  rw [hn]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hs ht ⊢
  have he : (n:ℝ)+1+128 = (n:ℝ)+128+1 := by ring
  rw [he]
  linarith

lemma f_tendsto_zero : Tendsto (fun n : ℕ => f (n+128)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).comp
      (tendsto_add_atTop_nat 128))
  simpa [f, Function.comp_def, Nat.cast_add] using h

/-- The exact original Stieltjes-limit/trapezoid input is discharged, unconditionally. -/
theorem stieltjes_trapezoid : BoxMellinInputs.v1.stieltjes_trapezoid := by
  let seq : ℕ → ℝ := fun n => BoxMellinInputs.v1.stieltjesSeq (n+128)
  let corr : ℕ → ℝ := fun n => seq n - f (n+128)/2
  have ha : Antitone seq := stieltjes_antitone
  have hm : Monotone corr := corrected_monotone
  have hb : BddBelow (range seq) := by
    refine ⟨corr 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hh := hm (Nat.zero_le n)
    have hp := f_nonneg (x:=((n+128:ℕ):ℝ)) (by exact_mod_cast (show 128 ≤ n+128 by omega))
    dsimp [corr] at hh ⊢
    simp only [Nat.cast_add, Nat.cast_ofNat] at hp
    linarith
  have ht : Tendsto seq atTop (𝓝 (⨅ n, seq n)) := tendsto_atTop_ciInf ha hb
  have htfull : Tendsto BoxMellinInputs.v1.stieltjesSeq atTop (𝓝 (⨅ n, seq n)) :=
    (tendsto_add_atTop_iff_nat 128).mp ht
  have hg : BoxMellinInputs.v1.gamma1 = ⨅ n, seq n := htfull.limUnder_eq
  have hcorr : Tendsto corr atTop (𝓝 (⨅ n, seq n)) := by
    simpa [corr] using ht.sub (f_tendsto_zero.div_const 2)
  have hlo : corr 0 ≤ ⨅ n, seq n :=
    ge_of_tendsto hcorr (Eventually.of_forall (fun n => hm (Nat.zero_le n)))
  constructor
  · simpa [hg] using htfull
  · rw [hg]
    have hc : corr 0 = BoxMellinInputs.v1.stieltjesSeq 128 - Real.log 128 / 256 := by
      dsimp [corr, seq, f]
      norm_num
      ring
    simpa [hc] using hlo

#print axioms stieltjes_trapezoid
end RHLimit.Stieltjes
