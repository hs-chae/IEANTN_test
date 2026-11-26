/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitMontgomeryVaughan
import ExplicitAtomicBV
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
noncomputable section
open Real Set
namespace RH080Next.Explicit

private theorem exp_difference_upper (A B : ℝ) : exp B-exp A ≤ exp B*(B-A) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (A-B)) (exp_pos B).le
  rw [←exp_add,show B+(A-B) = A by ring] at h
  nlinarith

/-- Actual weighted prime atoms pulled back to a logarithmic wing satisfy
the interval hypothesis of the proved continuous BV theorem. The density
and entrance constants retain the exact chosen physical block length ell. -/
theorem mv_log_coordinate_prefix_bound (hMV : SourceMontgomeryVaughan)
    (P : Finset ℕ) (x w : ℕ → ℝ) (Q d L R v0 s ell : ℝ)
    (hQ : 0 ≤ Q) (hd : 0 < d) (hs : 0 < s) (hell : 1 < ell)
    (hv0 : -R ≤ v0) (hv1 : v0+s ≤ R) (hpositive : R*d < L)
    (hPrime : ∀ p ∈ P, Nat.Prime p)
    (hPhysical : ∀ p ∈ P, (p:ℝ) = exp (L+d*(v0+s*x p)))
    (hWeight : ∀ p ∈ P, w p ≤ Q)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    atomicPrefix P x w b-atomicPrefix P x w a ≤
      (2*Q*d*s*exp (L+R*d)/log ell)*(b-a)+2*Q*ell/log ell := by
  let A := exp (L+d*(v0+s*a))
  let B := exp (L+d*(v0+s*b))
  have hds : 0 < d*s := mul_pos hd hs
  let S := P.filter (fun p => a < x p ∧ x p ≤ b)
  have hA : 1 < A := by
    apply one_lt_exp_iff.mpr
    nlinarith [mul_nonneg hs.le ha]
  have habarg : L+d*(v0+s*a) ≤ L+d*(v0+s*b) := by
    nlinarith [mul_nonneg hds.le (sub_nonneg.mpr hab)]
  have hAB : A ≤ B := exp_le_exp.mpr habarg
  have hSend : L+d*(v0+s*b) ≤ L+R*d := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hb)]
  have hgap : B-A ≤ d*s*exp (L+R*d)*(b-a) := by
    have h0 := exp_difference_upper (L+d*(v0+s*a)) (L+d*(v0+s*b))
    have hg : 0 ≤ (L+d*(v0+s*b))-(L+d*(v0+s*a)) := sub_nonneg.mpr habarg
    have h1 := mul_le_mul_of_nonneg_right (exp_le_exp.mpr hSend) hg
    nlinarith
  have hSP : ∀ p ∈ S, Nat.Prime p ∧ A < (p:ℝ) ∧ (p:ℝ) ≤ B := by
    intro p hp
    obtain ⟨hpP,hpa,hpb⟩ := Finset.mem_filter.mp hp
    refine ⟨hPrime p hpP,?_,?_⟩
    · rw [hPhysical p hpP]
      apply exp_lt_exp.mpr
      nlinarith [mul_pos hds (sub_pos.mpr hpa)]
    · rw [hPhysical p hpP]
      apply exp_le_exp.mpr
      nlinarith [mul_nonneg hds.le (sub_nonneg.mpr hpb)]
  have hcount := mv_finite_prime_interval_bound hMV S A B ell hA hAB hell hSP
  have hsum : atomicPrefix P x w b-atomicPrefix P x w a ≤ Q*(S.card:ℝ) := by
    rw [atomicPrefix_sub P x w a b hab]
    have heq : (∑ p ∈ P, if a < x p ∧ x p ≤ b then w p else 0) = ∑ p ∈ S, w p := by
      rw [Finset.sum_filter]
    rw [heq]
    calc
      (∑ p ∈ S, w p) ≤ ∑ _p ∈ S, Q := Finset.sum_le_sum (fun p hp => hWeight p (Finset.mem_filter.mp hp).1)
      _ = Q*(S.card:ℝ) := by simp [mul_comm]
  have hscaled := mul_le_mul_of_nonneg_left hcount hQ
  have hgap' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (by norm_num : (0:ℝ)≤2))
    (log_pos hell).le
  have hfinish := mul_le_mul_of_nonneg_left (add_le_add_right hgap' (2*ell/log ell)) hQ
  calc
    _ ≤ Q*(S.card:ℝ) := hsum
    _ ≤ Q*(2*(B-A)/log ell+2*ell/log ell) := hscaled
    _ ≤ Q*(2*(d*s*exp (L+R*d)*(b-a))/log ell+2*ell/log ell) := by simpa only [add_comm] using hfinish
    _ = _ := by ring

#print axioms mv_log_coordinate_prefix_bound
end RH080Next.Explicit
