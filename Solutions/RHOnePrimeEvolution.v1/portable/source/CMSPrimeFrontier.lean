/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import CMSGeometry
import CMSKernelNumerics

/-! Source-conditional finite-range one-prime frontier using the literal CMS
explicit obstruction (6.16). The source premise is new, explicit, and remains
literature-backed: this is NOT a derivation of (6.16) from the existing Green,
Nicolas or BPT interfaces. The actual numerical kernel ratio is independently
proved, and real-window geometry and continuum scalar coverage are proved here.
The source predicate preserves CLOSED endpoints. No strict-open theorem is
inferred from it without a separate interval transfer. -/
namespace RHOnePrime.CMSPrime
open Real Set
open RHOnePrime.CMSGeometry RHOnePrime.CMSScalar
set_option maxHeartbeats 0

/-- A closed real interval contains an actual natural prime. -/
def HasPrimeClosed (x y : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x ≤ (p : ℝ) ∧ (p : ℝ) ≤ y

/-- The precise source premise consumed by this module. CMS,
Fourier optimization and prime gaps, arXiv:1708.04122v2, Section 6,
(6.16), with lambda=9/10, x=exp(L), a=exp(L+t), 2*pi*Delta=t,
t=log(1+c*L/exp(L/2))/2. Their source range x>=4*10^18 contains
L>=44. The displayed J(F) is the actual ratio cmsJ, using their
Section4.3.1 identity ||H||_1=Si(pi)/2 and exact leakage integral.

This is a stated published analytic consequence with a full proof in the
source, not a new axiom or a claim that its source proof is formalized. In
particular the source's Brun--Titchmarsh decomposition, zero counting and
infinite tails remain inside THIS disclosed B-tier premise. -/
def SourceCMS616 : Prop :=
  RiemannHypothesis → ∀ L c : ℝ, 44 ≤ L → c ∈ Icc (1 / 2 : ℝ) 1 →
    ¬ HasPrimeClosed (exp L) (exp L + c * sqrt (exp L) * L) →
      RHOnePrimeEvolution.CMSNumerics.cmsJ * mainScale c L ≤ logScale c L + 29 / 25

/-- The exact source premise, actual kernel calculation and scalar continuum
proof imply an actual prime. The interval remains closed on both ends. -/
theorem closed_prime_from_margin (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {c L : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1) (hL : 44 ≤ L)
    (hm : 0 < margin c L) :
    HasPrimeClosed (exp L) (exp L + c * sqrt (exp L) * L) := by
  by_contra hp
  have hob := hCMS rh L c hL ⟨by linarith, hc1⟩ hp
  exact obstruction_impossible
    RHOnePrimeEvolution.CMSNumerics.actual_cmsJ_lower
    (mainScale_nonneg hc hc1 hL) (mainScale_lower hc hc1 hL)
    (logScale_upper hc hc1 hL) hm hob

/-- All-real closed one-prime interval, with all source assumptions displayed. -/
theorem closed_prime_0877 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hx : exp 44 ≤ x) :
    HasPrimeClosed x (x + (877 / 1000) * sqrt x * log x) := by
  have hx0 : 0 < x := (exp_pos 44).trans_le hx
  have hL : 44 ≤ log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have h := closed_prime_from_margin hCMS rh (by norm_num : (4 / 5 : ℝ) ≤ 877 / 1000)
    (by norm_num) hL (tail_0877 hL)
  simpa only [Real.exp_log hx0] using h

/-- First finite slab: a coefficient below the asymptotic .8358 benchmark,
only on this explicit bounded range; no asymptotic domination is asserted. -/
theorem closed_prime_083 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 60) :
    HasPrimeClosed x (x + (83 / 100) * sqrt x * log x) := by
  have hx0 : 0 < x := (exp_pos 44).trans_le hlo
  have hL : 44 ≤ log x := (Real.le_log_iff_exp_le hx0).mpr hlo
  have hU : log x ≤ 60 := (Real.log_le_iff_le_exp hx0).mpr hhi
  have h := closed_prime_from_margin hCMS rh (by norm_num : (4 / 5 : ℝ) ≤ 83 / 100)
    (by norm_num) hL (slab_083 hL hU)
  simpa only [Real.exp_log hx0] using h

lemma margin_mono_coefficient {c d L : ℝ} (hcd : c ≤ d) (hL : 0 ≤ L) :
    margin c L ≤ margin d L := by
  have hj : 0 ≤ jFloor := by norm_num [jFloor]
  have hm := mul_nonneg (mul_nonneg hj (sub_nonneg.mpr hcd)) hL
  unfold margin effectiveCost
  nlinarith

/-- A generic slab-transfer consumer for every proved finite coefficient. -/
theorem closed_prime_on_slab (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {c A B x : ℝ} (hA : 44 ≤ A) (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1)
    (hslab : ∀ L : ℝ, A ≤ L → L ≤ B → 0 < margin c L)
    (hlo : exp A ≤ x) (hhi : x ≤ exp B) :
    HasPrimeClosed x (x + c * sqrt x * log x) := by
  have hx0 : 0 < x := (exp_pos A).trans_le hlo
  have hL : A ≤ log x := (Real.le_log_iff_exp_le hx0).mpr hlo
  have hU : log x ≤ B := (Real.log_le_iff_le_exp hx0).mpr hhi
  have h := closed_prime_from_margin hCMS rh hc hc1 (hA.trans hL) (hslab _ hL hU)
  simpa only [Real.exp_log hx0] using h

#print axioms closed_prime_from_margin
#print axioms closed_prime_0877
#print axioms closed_prime_083
#print axioms closed_prime_on_slab
#check @closed_prime_0877
#check @closed_prime_083
end RHOnePrime.CMSPrime
