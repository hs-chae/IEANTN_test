/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ActualPrimeWings
import ActualPrimePowerAllowance
set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Primal
open RH080Next.Explicit

def centralPrimePart (nodes : List ℚ) (m : ℕ) (d L : ℝ) : ℝ :=
  ∑ p ∈ realPrimesIoc (exp (L-d)) (exp (L+d)),
    ArithmeticFunction.vonMangoldt p*mellinArithmeticWeight nodes m d L p

private theorem natural_actual_term (nodes : List ℚ) (m : ℕ) (d L : ℝ) (n : CMSPrimeIndex) :
    weightedMangoldtFamily nodes m d L n=weightedNaturalWindow (affineSpectrum nodes m) d L (n:ℕ) := by
  unfold weightedMangoldtFamily mellinArithmeticWeight weightedNaturalWindow
  ring

private theorem raw_support_two (W : ℝ → ℝ) (d L : ℝ) :
    Function.support (weightedNaturalWindow W d L)⊆{n : ℕ | 2≤n} := by
  intro n hn
  by_contra h
  change ¬2≤n at h
  have hcases : n=0 ∨ n=1 := by omega
  rcases hcases with h0 | h1
  · subst n
    simpa [Function.mem_support,weightedNaturalWindow] using hn
  · subst n
    simpa [Function.mem_support,weightedNaturalWindow] using hn

private theorem raw_zero_outside_envelope (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (d L : ℝ) (hd : 0<d)
    (n : ℕ) (hn : n∉Finset.Icc 2 (Nat.floor (exp (L+radius nodes m*d)))) :
    weightedNaturalWindow (affineSpectrum nodes m) d L n=0 := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n=0
  · simp [weightedNaturalWindow,hΛ]
  by_cases hW : affineSpectrum nodes m ((log (n:ℝ)-L)/d)=0
  · simp [weightedNaturalWindow,hW]
  have hpow := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  have hn2 : 2≤n := by have h0:=hpow.ne_zero; have h1:=hpow.ne_one; omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have harg : |(log (n:ℝ)-L)/d|<radius nodes m := by
    apply lt_of_not_ge
    intro h
    exact hW (affineSpectrum_eq_zero_of_radius_le nodes m hlen hm _ h)
  have hhi : log (n:ℝ)≤L+radius nodes m*d := by
    have h := (div_lt_iff₀ hd).mp (abs_lt.mp harg).2
    linarith
  have hbound : n≤Nat.floor (exp (L+radius nodes m*d)) :=
    (Nat.le_floor_iff (exp_pos _).le).mpr ((log_le_iff_le_exp hn0).mp hhi)
  exact False.elim (hn (Finset.mem_Icc.mpr ⟨hn2,hbound⟩))

private theorem prime_raw_zero_outside_physical (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (d L : ℝ) (hd : 0<d)
    (n : ℕ) (hn : n∉realPrimesIoc (exp (L-radius nodes m*d)) (exp (L+radius nodes m*d))) :
    (if Nat.Prime n then weightedNaturalWindow (affineSpectrum nodes m) d L n else 0)=0 := by
  by_cases hp : Nat.Prime n
  · rw [ite_eq_left hp]
    by_cases hW : affineSpectrum nodes m ((log (n:ℝ)-L)/d)=0
    · simp [weightedNaturalWindow,hW]
    have hn0 : (0:ℝ)<n := by exact_mod_cast hp.pos
    have harg : |(log (n:ℝ)-L)/d|<radius nodes m := by
      apply lt_of_not_ge
      intro h
      exact hW (affineSpectrum_eq_zero_of_radius_le nodes m hlen hm _ h)
    have hlo : L-radius nodes m*d<log (n:ℝ) := by
      have h := (lt_div_iff₀ hd).mp (abs_lt.mp harg).1
      linarith
    have hhi : log (n:ℝ)≤L+radius nodes m*d := by
      have h := (div_lt_iff₀ hd).mp (abs_lt.mp harg).2
      linarith
    exact False.elim (hn ((mem_realPrimesIoc _ _ (exp_pos _).le (exp_pos _).le n).mpr
      ⟨hp,(lt_log_iff_exp_lt hn0).mp hlo,(log_le_iff_le_exp hn0).mp hhi⟩))
  · simp [hp]

private theorem sum_realPrimesIoc_split (f : ℕ → ℝ) (a b c : ℝ) (hab : a≤b) (hbc : b≤c) :
    (∑ p ∈ realPrimesIoc a c,f p)=
      (∑ p ∈ realPrimesIoc a b,f p)+(∑ p ∈ realPrimesIoc b c,f p) := by
  unfold realPrimesIoc
  rw [Finset.sum_sdiff_eq_sub (Nat.primesLE_mono (Nat.floor_mono (hab.trans hbc))),
    Finset.sum_sdiff_eq_sub (Nat.primesLE_mono (Nat.floor_mono hab)),
    Finset.sum_sdiff_eq_sub (Nat.primesLE_mono (Nat.floor_mono hbc))]
  ring

private theorem raw_prime_le_positive (nodes : List ℚ) (m : ℕ) (d L : ℝ)
    (p : ℕ) (hp : Nat.Prime p) :
    weightedNaturalWindow (affineSpectrum nodes m) d L p≤primePositiveTerm nodes m d L p := by
  have hw : 0≤log (p:ℝ)/sqrt (p:ℝ) :=
    div_nonneg (log_nonneg (by exact_mod_cast hp.one_le)) (sqrt_nonneg _)
  unfold weightedNaturalWindow primePositiveTerm primeWeight spectralCoordinate
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  calc
    _ = (log (p:ℝ)/sqrt (p:ℝ))*affineSpectrum nodes m ((log (p:ℝ)-L)/d) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hw

/-- Actual arithmetic sum split. The central interval is left-open/right-closed;
its lower boundary prime goes to the left wing and its upper boundary prime to
the center. Outer support endpoints have genuinely zero spectrum. -/
theorem actual_full_arithmetic_split (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hmN : m<nodes.length-1)
    (d L : ℝ) (hd : 0<d) :
    Summable (weightedMangoldtFamily nodes m d L) ∧
      (∑' n : CMSPrimeIndex,weightedMangoldtFamily nodes m d L n)≤
        centralPrimePart nodes m d L+
        (∑ p ∈ leftWingPrimes d L (radius nodes m),primePositiveTerm nodes m d L p)+
        (∑ p ∈ rightWingPrimes d L (radius nodes m),primePositiveTerm nodes m d L p)+
        (∑' n : CMSPrimeIndex,actualNonprimeMangoldtFamily nodes m d L n) := by
  let f : ℕ → ℝ := weightedNaturalWindow (affineSpectrum nodes m) d L
  let fp : ℕ → ℝ := fun n => if Nat.Prime n then f n else 0
  let fn : ℕ → ℝ := fun n => if Nat.Prime n then 0 else f n
  let fa : ℕ → ℝ := nonprimeNaturalWindow (affineSpectrum nodes m) d L
  let S : Finset ℕ := Finset.Icc 2 (Nat.floor (exp (L+radius nodes m*d)))
  have hz := raw_zero_outside_envelope nodes m hlen hm d L hd
  have hs : Summable f := summable_of_ne_finset_zero hz
  have hsp : Summable fp := summable_of_ne_finset_zero (s := S) (fun n hn => by
    dsimp [fp]; rw [show f n=0 from hz n hn]; split_ifs <;> rfl)
  have hsn : Summable fn := summable_of_ne_finset_zero (s := S) (fun n hn => by
    dsimp [fn]; rw [show f n=0 from hz n hn]; split_ifs <;> rfl)
  have hsa : Summable fa := summable_of_ne_finset_zero (s := S) (fun n hn => by
    unfold fa nonprimeNaturalWindow
    rw [hz n hn]
    split_ifs <;> simp)
  have hActual : (fun n : CMSPrimeIndex => weightedMangoldtFamily nodes m d L n)=
      fun n : CMSPrimeIndex => f (n:ℕ) := by funext n; exact natural_actual_term nodes m d L n
  have hSumActual : (∑' n : CMSPrimeIndex,weightedMangoldtFamily nodes m d L n)=∑' n : ℕ,f n := by
    rw [hActual]
    exact tsum_subtype_eq_of_support_subset (raw_support_two _ _ _)
  have hAbsActual : (∑' n : CMSPrimeIndex,actualNonprimeMangoldtFamily nodes m d L n)=∑' n : ℕ,fa n := by
    have he : actualNonprimeMangoldtFamily nodes m d L=fun n : CMSPrimeIndex => fa (n:ℕ) := by
      funext n
      unfold actualNonprimeMangoldtFamily fa nonprimeNaturalWindow
      rw [natural_actual_term]
    rw [he]
    apply tsum_subtype_eq_of_support_subset
    intro n hn
    by_contra h
    change ¬2≤n at h
    have hn0 : n=0 ∨ n=1 := by omega
    rcases hn0 with h0 | h1 <;> subst n <;>
      simpa [Function.mem_support,fa,nonprimeNaturalWindow,weightedNaturalWindow] using hn
  have hsplit : f=fp+fn := by
    funext n
    dsimp [fp,fn]
    split_ifs <;> simp
  have hNon : (∑' n : ℕ,fn n)≤∑' n : ℕ,fa n := by
    apply hsn.tsum_le_tsum _ hsa
    intro n
    dsimp [fn,fa,nonprimeNaturalWindow]
    split_ifs
    · rfl
    · exact le_abs_self _
  have hPrimeSum : (∑' n : ℕ,fp n)=
      ∑ p ∈ realPrimesIoc (exp (L-radius nodes m*d)) (exp (L+radius nodes m*d)),f p := by
    rw [tsum_eq_sum (prime_raw_zero_outside_physical nodes m hlen hm d L hd)]
    apply Finset.sum_congr rfl
    intro p hp
    have hprime := ((mem_realPrimesIoc _ _ (exp_pos _).le (exp_pos _).le p).mp hp).1
    exact ite_eq_left hprime
  have hR : (1:ℝ)<radius nodes m := by
    unfold radius
    have hm' : (0:ℝ)<m := by exact_mod_cast hm
    apply (lt_div_iff₀ hm').mpr
    simpa using (show (m:ℝ)<((nodes.length-1:ℕ):ℝ) by exact_mod_cast hmN)
  have hab : exp (L-radius nodes m*d)≤exp (L-d) := exp_le_exp.mpr (by nlinarith)
  have hbc : exp (L-d)≤exp (L+d) := exp_le_exp.mpr (by linarith)
  have hcd : exp (L+d)≤exp (L+radius nodes m*d) := exp_le_exp.mpr (by nlinarith)
  have hPhysicalSplit : (∑' n : ℕ,fp n)=
      (∑ p ∈ leftWingPrimes d L (radius nodes m),f p)+
      (∑ p ∈ realPrimesIoc (exp (L-d)) (exp (L+d)),f p)+
      (∑ p ∈ rightWingPrimes d L (radius nodes m),f p) := by
    rw [hPrimeSum,sum_realPrimesIoc_split f _ _ _ (hab.trans hbc) hcd,
      sum_realPrimesIoc_split f _ _ _ hab hbc]
    rfl
  have hLeft : (∑ p ∈ leftWingPrimes d L (radius nodes m),f p)≤
      ∑ p ∈ leftWingPrimes d L (radius nodes m),primePositiveTerm nodes m d L p := by
    apply Finset.sum_le_sum
    intro p hp
    exact raw_prime_le_positive nodes m d L p
      (((mem_realPrimesIoc _ _ (exp_pos _).le (exp_pos _).le p).mp hp).1)
  have hRight : (∑ p ∈ rightWingPrimes d L (radius nodes m),f p)≤
      ∑ p ∈ rightWingPrimes d L (radius nodes m),primePositiveTerm nodes m d L p := by
    apply Finset.sum_le_sum
    intro p hp
    exact raw_prime_le_positive nodes m d L p
      (((mem_realPrimesIoc _ _ (exp_pos _).le (exp_pos _).le p).mp hp).1)
  have hCenter : (∑ p ∈ realPrimesIoc (exp (L-d)) (exp (L+d)),f p)=centralPrimePart nodes m d L := by
    apply Finset.sum_congr rfl
    intro p hp
    unfold f weightedNaturalWindow mellinArithmeticWeight
    ring
  refine ⟨(hs.subtype (fun n : ℕ => 2≤n)).congr (fun n => (natural_actual_term nodes m d L n).symm),?_⟩
  rw [hSumActual,hsplit]
  simp only [Pi.add_apply]
  rw [hsp.tsum_add hsn,hPhysicalSplit,hCenter,hAbsActual]
  linarith

/-- Both actual exterior prime wings are now bounded from the original general
MV source input, and the actual arithmetic sum is connected to the central
finite prime count plus the separately proved nonprime allowance. -/
theorem actual_full_arithmetic_wing_bound (hMV : SourceMontgomeryVaughan)
    (nodes : List ℚ) (m : ℕ) (hlen : 2≤nodes.length) (hm : 0<m)
    (hmN : m<nodes.length-1) (hlast : node nodes (nodes.length-1)=0)
    (d L ell : ℝ) (hd : 0<d) (hpositive : radius nodes m*d<L) (hell : 1<ell) :
    Summable (weightedMangoldtFamily nodes m d L) ∧
      (∑' n : CMSPrimeIndex,weightedMangoldtFamily nodes m d L n)≤
        centralPrimePart nodes m d L+
        (2*exteriorPrimeWeight d L (radius nodes m)*d*exp (L+radius nodes m*d)/log ell)*
          IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)+
        (4*exteriorPrimeWeight d L (radius nodes m)*ell/log ell)*nodalH nodes m+
        (∑' n : CMSPrimeIndex,actualNonprimeMangoldtFamily nodes m d L n) := by
  obtain ⟨hs,hSplit⟩ := actual_full_arithmetic_split nodes m hlen hm hmN d L hd
  have hWings := actual_two_prime_wings_le hMV nodes m hlen hm hmN hlast d L ell hd hpositive hell
  exact ⟨hs,by linarith⟩

#print axioms actual_full_arithmetic_split
#print axioms actual_full_arithmetic_wing_bound
end RH080Next.Primal
