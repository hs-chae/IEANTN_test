/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AffineWingBV
import ExplicitMVAtomic
import ExplicitPrimeWeights
set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Primal
open RH080Next.Explicit

def spectralCoordinate (d L : ℝ) (p : ℕ) : ℝ := (log (p:ℝ)-L)/d
def primeWingCoordinate (d L v0 s : ℝ) (p : ℕ) : ℝ := (spectralCoordinate d L p-v0)/s
def primeWeight (p : ℕ) : ℝ := log (p:ℝ)/sqrt (p:ℝ)
def primePositiveTerm (nodes : List ℚ) (m : ℕ) (d L : ℝ) (p : ℕ) : ℝ :=
  primeWeight p*max 0 (affineSpectrum nodes m (spectralCoordinate d L p))
def leftWingPrimes (d L R : ℝ) : Finset ℕ := realPrimesIoc (exp (L-R*d)) (exp (L-d))
def rightWingPrimes (d L R : ℝ) : Finset ℕ := realPrimesIoc (exp (L+d)) (exp (L+R*d))

private theorem physical_primeWingCoordinate (p : ℕ) (hp : Nat.Prime p)
    (d L v0 s : ℝ) (hd : 0<d) (hs : 0<s) :
    (p:ℝ)=exp (L+d*(v0+s*primeWingCoordinate d L v0 s p)) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  unfold primeWingCoordinate spectralCoordinate
  rw [show L+d*(v0+s*(((log (p:ℝ)-L)/d-v0)/s))=log (p:ℝ) by field_simp; ring,
    exp_log hp0]

private theorem primeWeight_nonneg (p : ℕ) (hp : Nat.Prime p) : 0≤primeWeight p := by
  unfold primeWeight
  exact div_nonneg (log_nonneg (by exact_mod_cast hp.one_le)) (sqrt_nonneg _)

private theorem support_radius_gt_one (nodes : List ℚ) (m : ℕ)
    (hm : 0<m) (hmN : m<nodes.length-1) : 1<radius nodes m := by
  unfold radius
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  apply (lt_div_iff₀ hm').mpr
  simpa using (show (m:ℝ)<((nodes.length-1:ℕ):ℝ) by exact_mod_cast hmN)

/-- Actual right-wing primes, weights and logarithmic coordinates satisfy all
hypotheses of the source MV interval bound and the proved atomic BV consumer. -/
theorem actual_right_prime_wing_le (hMV : SourceMontgomeryVaughan)
    (nodes : List ℚ) (m : ℕ) (hlen : 2≤nodes.length) (hm : 0<m)
    (hmN : m<nodes.length-1) (hlast : node nodes (nodes.length-1)=0)
    (d L ell : ℝ) (hd : 0<d) (hpositive : radius nodes m*d<L) (hell : 1<ell) :
    (∑ p ∈ rightWingPrimes d L (radius nodes m),primePositiveTerm nodes m d L p)≤
      (exteriorPrimeWeight d L (radius nodes m)*d*exp (L+radius nodes m*d)/log ell)*
        IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)+
      (2*exteriorPrimeWeight d L (radius nodes m)*ell/log ell)*nodalH nodes m := by
  let R := radius nodes m
  let P := rightWingPrimes d L R
  let x := primeWingCoordinate d L 1 (R-1)
  let Q := exteriorPrimeWeight d L R
  have hR : 1<R := support_radius_gt_one nodes m hm hmN
  have hs : 0<R-1 := by linarith
  have hlog : 0<log ell := log_pos hell
  have hδ : 0≤R*d := mul_nonneg (by linarith) hd.le
  have hQ : 0≤Q := by unfold Q exteriorPrimeWeight; have hL : 0<L := hδ.trans_lt hpositive; positivity
  have hPrime (p : ℕ) (hp : p∈P) : Nat.Prime p :=
    ((mem_realPrimesIoc _ _ (exp_pos _).le (exp_pos _).le p).mp hp).1
  have hPhys (p : ℕ) (hp : p∈P) : (p:ℝ)=exp (L+d*(1+(R-1)*x p)) :=
    physical_primeWingCoordinate p (hPrime p hp) d L 1 (R-1) hd hs
  have hArg (p : ℕ) (hp : p∈P) : 1<spectralCoordinate d L p ∧ spectralCoordinate d L p≤R := by
    obtain ⟨hpp,hlo,hhi⟩ := (mem_realPrimesIoc _ _ (exp_pos _).le (exp_pos _).le p).mp hp
    have hp0 : (0:ℝ)<p := by exact_mod_cast hpp.pos
    have hl := (lt_log_iff_exp_lt hp0).mpr hlo
    have hu := (log_le_iff_le_exp hp0).mpr hhi
    unfold spectralCoordinate
    exact ⟨(lt_div_iff₀ hd).mpr (by linarith),(div_le_iff₀ hd).mpr (by linarith)⟩
  have hx (p : ℕ) (hp : p∈P) : 0<x p ∧ x p≤1 := by
    obtain ⟨hl,hu⟩ := hArg p hp
    exact ⟨div_pos (by linarith) hs,(div_le_one hs).mpr (by linarith)⟩
  have hWeight (p : ℕ) (hp : p∈P) : primeWeight p≤Q := by
    obtain ⟨hpp,hlo,hhi⟩ := (mem_realPrimesIoc _ _ (exp_pos _).le (exp_pos _).le p).mp hp
    apply prime_log_weight_le_support d L R hd.le (by linarith) hpositive p hpp _ hhi
    exact (exp_le_exp.mpr (by nlinarith)).trans hlo.le
  have hc := mv_log_coordinate_prefix_bound hMV P x primeWeight Q d L R 1 (R-1) ell
    hQ hd hs hell (by linarith) (by linarith) hpositive hPrime hPhys hWeight
  have h := rightWing_atomic_BV_bound P x primeWeight nodes m hlen hm hmN hlast
    (2*Q*d*(R-1)*exp (L+R*d)/log ell) (2*Q*ell/log ell)
    (by positivity) (by positivity) hx (fun p hp => primeWeight_nonneg p (hPrime p hp)) hc
  have hterm (p : ℕ) : primeWeight p*positiveRightWing nodes m (x p)=primePositiveTerm nodes m d L p := by
    unfold positiveRightWing primePositiveTerm x primeWingCoordinate
    congr 2
    congr 1
    change 1+(R-1)*((spectralCoordinate d L p-1)/(R-1))=spectralCoordinate d L p
    field_simp
    <;> ring
  simp_rw [hterm] at h
  apply h.trans_eq
  change (2*Q*d*(R-1)*exp (L+R*d)/log ell)*
    (IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)/(2*(R-1)))+
    (2*Q*ell/log ell)*nodalH nodes m=_
  field_simp
  <;> ring

/-- Actual left wing includes v=-1; its outer endpoint is excluded, where the
supported spectrum vanishes. No endpoint mass is lost or charged twice. -/
theorem actual_left_prime_wing_le (hMV : SourceMontgomeryVaughan)
    (nodes : List ℚ) (m : ℕ) (hlen : 2≤nodes.length) (hm : 0<m)
    (hmN : m<nodes.length-1) (hlast : node nodes (nodes.length-1)=0)
    (d L ell : ℝ) (hd : 0<d) (hpositive : radius nodes m*d<L) (hell : 1<ell) :
    (∑ p ∈ leftWingPrimes d L (radius nodes m),primePositiveTerm nodes m d L p)≤
      (exteriorPrimeWeight d L (radius nodes m)*d*exp (L+radius nodes m*d)/log ell)*
        IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)+
      (2*exteriorPrimeWeight d L (radius nodes m)*ell/log ell)*nodalH nodes m := by
  let R := radius nodes m
  let P := leftWingPrimes d L R
  let x := primeWingCoordinate d L (-R) (R-1)
  let Q := exteriorPrimeWeight d L R
  have hR : 1<R := support_radius_gt_one nodes m hm hmN
  have hs : 0<R-1 := by linarith
  have hlog : 0<log ell := log_pos hell
  have hδ : 0≤R*d := mul_nonneg (by linarith) hd.le
  have hQ : 0≤Q := by unfold Q exteriorPrimeWeight; have hL : 0<L := hδ.trans_lt hpositive; positivity
  have hPrime (p : ℕ) (hp : p∈P) : Nat.Prime p :=
    ((mem_realPrimesIoc _ _ (exp_pos _).le (exp_pos _).le p).mp hp).1
  have hPhys (p : ℕ) (hp : p∈P) : (p:ℝ)=exp (L+d*(-R+(R-1)*x p)) :=
    physical_primeWingCoordinate p (hPrime p hp) d L (-R) (R-1) hd hs
  have hArg (p : ℕ) (hp : p∈P) : -R<spectralCoordinate d L p ∧ spectralCoordinate d L p≤-1 := by
    obtain ⟨hpp,hlo,hhi⟩ := (mem_realPrimesIoc _ _ (exp_pos _).le (exp_pos _).le p).mp hp
    have hp0 : (0:ℝ)<p := by exact_mod_cast hpp.pos
    have hl := (lt_log_iff_exp_lt hp0).mpr hlo
    have hu := (log_le_iff_le_exp hp0).mpr hhi
    unfold spectralCoordinate
    exact ⟨(lt_div_iff₀ hd).mpr (by linarith),(div_le_iff₀ hd).mpr (by linarith)⟩
  have hx (p : ℕ) (hp : p∈P) : 0<x p ∧ x p≤1 := by
    obtain ⟨hl,hu⟩ := hArg p hp
    exact ⟨div_pos (by linarith) hs,(div_le_one hs).mpr (by linarith)⟩
  have hWeight (p : ℕ) (hp : p∈P) : primeWeight p≤Q := by
    obtain ⟨hpp,hlo,hhi⟩ := (mem_realPrimesIoc _ _ (exp_pos _).le (exp_pos _).le p).mp hp
    apply prime_log_weight_le_support d L R hd.le (by linarith) hpositive p hpp hlo.le
    exact hhi.trans (exp_le_exp.mpr (by nlinarith))
  have hc := mv_log_coordinate_prefix_bound hMV P x primeWeight Q d L R (-R) (R-1) ell
    hQ hd hs hell le_rfl (by linarith) hpositive hPrime hPhys hWeight
  have h := leftWing_atomic_BV_bound P x primeWeight nodes m hlen hm hmN hlast
    (2*Q*d*(R-1)*exp (L+R*d)/log ell) (2*Q*ell/log ell)
    (by positivity) (by positivity) hx (fun p hp => primeWeight_nonneg p (hPrime p hp)) hc
  have hterm (p : ℕ) : primeWeight p*positiveLeftWing nodes m (x p)=primePositiveTerm nodes m d L p := by
    unfold positiveLeftWing primePositiveTerm x primeWingCoordinate
    congr 2
    congr 1
    change -R+(R-1)*((spectralCoordinate d L p-(-R))/(R-1))=spectralCoordinate d L p
    field_simp
    <;> ring
  simp_rw [hterm] at h
  apply h.trans_eq
  change (2*Q*d*(R-1)*exp (L+R*d)/log ell)*
    (IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)/(2*(R-1)))+
    (2*Q*ell/log ell)*nodalH nodes m=_
  field_simp
  <;> ring

theorem actual_two_prime_wings_le (hMV : SourceMontgomeryVaughan)
    (nodes : List ℚ) (m : ℕ) (hlen : 2≤nodes.length) (hm : 0<m)
    (hmN : m<nodes.length-1) (hlast : node nodes (nodes.length-1)=0)
    (d L ell : ℝ) (hd : 0<d) (hpositive : radius nodes m*d<L) (hell : 1<ell) :
    (∑ p ∈ leftWingPrimes d L (radius nodes m),primePositiveTerm nodes m d L p)+
      (∑ p ∈ rightWingPrimes d L (radius nodes m),primePositiveTerm nodes m d L p)≤
      (2*exteriorPrimeWeight d L (radius nodes m)*d*exp (L+radius nodes m*d)/log ell)*
        IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)+
      (4*exteriorPrimeWeight d L (radius nodes m)*ell/log ell)*nodalH nodes m := by
  have h := add_le_add
    (actual_left_prime_wing_le hMV nodes m hlen hm hmN hlast d L ell hd hpositive hell)
    (actual_right_prime_wing_le hMV nodes m hlen hm hmN hlast d L ell hd hpositive hell)
  exact h.trans_eq (by ring)

#print axioms actual_right_prime_wing_le
#print axioms actual_left_prime_wing_le
#print axioms actual_two_prime_wings_le
end RH080Next.Primal
