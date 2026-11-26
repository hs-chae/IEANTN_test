/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PrimePowerWindowBounds
import ExplicitMellinIdentity
import ExplicitPrimePowerAllowance
set_option autoImplicit false
noncomputable section
open Real Set Filter MeasureTheory
namespace RH080Next.Primal
open RH080Next.Explicit

/-- This is the actual arithmetic family occurring in the proved Mellin
identity, with only its nonprime indices retained and absolute values taken. -/
def actualNonprimeMangoldtFamily (nodes : List ℚ) (m : ℕ) (d L : ℝ)
    (n : CMSPrimeIndex) : ℝ :=
  if Nat.Prime (n:ℕ) then 0 else |weightedMangoldtFamily nodes m d L n|

private theorem actual_nonprime_term_exact (nodes : List ℚ) (m : ℕ) (d L : ℝ)
    (n : CMSPrimeIndex) :
    actualNonprimeMangoldtFamily nodes m d L n=
      nonprimeNaturalWindow (affineSpectrum nodes m) d L (n:ℕ) := by
  unfold actualNonprimeMangoldtFamily nonprimeNaturalWindow
  by_cases hp : Nat.Prime (n:ℕ)
  · simp [hp]
  · rw [ite_eq_right hp,ite_eq_right hp]
    congr 1
    unfold weightedMangoldtFamily mellinArithmeticWeight weightedNaturalWindow
    ring

private theorem natural_nonprime_support (W : ℝ → ℝ) (d L : ℝ) :
    Function.support (nonprimeNaturalWindow W d L)⊆{n : ℕ | 2≤n} := by
  intro n hn
  by_contra h
  have hn2 : n<2 := Nat.lt_of_not_ge h
  have hcases : n=0 ∨ n=1 := by omega
  rcases hcases with h0 | h1
  · subst n
    simpa [Function.mem_support,nonprimeNaturalWindow,weightedNaturalWindow] using hn
  · subst n
    simpa [Function.mem_support,nonprimeNaturalWindow,weightedNaturalWindow] using hn

/-- Full actual nonprime-Mangoldt sum, including convergence, bounded using only
proved support, prime-power arithmetic and the physical log-window geometry. -/
theorem actual_nonprimeMangoldt_window_bound (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (d L M : ℝ)
    (hd : 0<d) (hM : 0≤M) (hupper : 0≤L+radius nodes m*d)
    (hbound : ∀ v : ℝ, |affineSpectrum nodes m v|≤M) :
    Summable (actualNonprimeMangoldtFamily nodes m d L) ∧
      (∑' n : CMSPrimeIndex, actualNonprimeMangoldtFamily nodes m d L n)≤
        primePowerWindowAllowance M L (radius nodes m*d) := by
  have hR : 0≤radius nodes m := by unfold radius; positivity
  obtain ⟨hs,he⟩ := tsum_nonprimeNaturalWindow_le (affineSpectrum nodes m)
    d L (radius nodes m) M hd hR hM hupper
    (affineSpectrum_eq_zero_of_radius_le nodes m hlen hm) hbound
  have hTerm : actualNonprimeMangoldtFamily nodes m d L=
      fun n : CMSPrimeIndex => nonprimeNaturalWindow (affineSpectrum nodes m) d L (n:ℕ) := by
    funext n
    exact actual_nonprime_term_exact nodes m d L n
  have hsumEq : (∑' n : CMSPrimeIndex,
      nonprimeNaturalWindow (affineSpectrum nodes m) d L (n:ℕ))=
      ∑' n : ℕ, nonprimeNaturalWindow (affineSpectrum nodes m) d L n :=
    tsum_subtype_eq_of_support_subset (natural_nonprime_support _ _ _)
  rw [hTerm]
  exact ⟨hs.subtype _,hsumEq.trans_le he⟩

/-- The original full continuous parameter domain has actual nonprime
prime-power loss below0.001. This is a proved mathematical bound, not a
numerical source assumption or an evaluated finite test grid. -/
theorem actual_nonprimeMangoldt_lt (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (c t M : ℝ)
    (hc : (1/2:ℝ)≤c) (hc1 : c≤1) (ht : 42≤t)
    (hR : radius nodes m≤10) (hM0 : 0≤M) (hM : M≤2)
    (hbound : ∀ v : ℝ, |affineSpectrum nodes m v|≤M) :
    Summable (actualNonprimeMangoldtFamily nodes m (halfLogWidth c t) (t+halfLogWidth c t)) ∧
      (∑' n : CMSPrimeIndex,
        actualNonprimeMangoldtFamily nodes m (halfLogWidth c t) (t+halfLogWidth c t) n)<
          (1/1000:ℝ) := by
  have hd := (halfLogWidth_bounds c t hc hc1 ht).1
  have hR0 : 0≤radius nodes m := by unfold radius; positivity
  obtain ⟨hs,he⟩ := actual_nonprimeMangoldt_window_bound nodes m hlen hm
    (halfLogWidth c t) (t+halfLogWidth c t) M hd hM0 (by positivity) hbound
  refine ⟨hs,he.trans_lt ?_⟩
  unfold primePowerWindowAllowance
  rw [show t+halfLogWidth c t+radius nodes m*halfLogWidth c t=
    t+(1+radius nodes m)*halfLogWidth c t by ring,
    show t+halfLogWidth c t-radius nodes m*halfLogWidth c t=
    t+(1-radius nodes m)*halfLogWidth c t by ring]
  exact primepower_window_allowance_lt c t (radius nodes m) M
    hc hc1 ht hR0 hR hM0 hM

#print axioms actual_nonprimeMangoldt_window_bound
#print axioms actual_nonprimeMangoldt_lt
end RH080Next.Primal
