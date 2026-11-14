/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SynergyBasis.PositiveModel
import SynergyAnalytic.LogBounds
namespace SynergyBasis.Positive
open ScopedNumerical ScopedNumerical.ProofBox
open SynergyBasis.RealBox
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Forward loop states (term,sum), matching atanh2's source update order. -/
def series (r : ProofBox) : Nat → ProofBox × ProofBox
  | 0 => (r,zero)
  | k+1 => let st := series r k
           (mul p st.1 (mul p r r),add st.2 (divN st.1 (2*k+1)))
def atanh2 (r : ProofBox) : ProofBox :=
  let b := add (series r 80).2 (series r 80).2
  ⟨b.lo,b.hi+1⟩

noncomputable def realSeries (x : ℝ) (k : Nat) : ℝ :=
  ∑ j ∈ Finset.range k, x^(2*j+1)/((2*j+1:Nat):ℝ)

theorem series_sound {r : ProofBox} {x : ℝ} (hr : RealBox.Contains p r x) (n : Nat) :
    RealBox.Contains p (series r n).1 (x^(2*n+1)) ∧
    RealBox.Contains p (series r n).2 (realSeries x n) := by
  induction n with
  | zero => simpa [series,realSeries] using And.intro hr zero_sound
  | succ k ih =>
    have ht := RealBox.mul_sound ih.1 (RealBox.mul_sound hr hr)
    have he : (x^(2*k+1))*(x*x) = x^(2*(k+1)+1) := by
      rw [←pow_two,←pow_add]; congr 1 <;> omega
    rw [he] at ht
    have hs := RealBox.add_sound ih.2 (divN_sound ih.1 (by omega : 0<2*k+1))
    have hse : realSeries x k+x^(2*k+1)/((2*k+1:Nat):ℝ) = realSeries x (k+1) := by
      simp only [realSeries,Finset.sum_range_succ]
    rw [hse] at hs
    exact ⟨ht,hs⟩

theorem atanh2_sound {r : ProofBox} {x : ℝ} (hr : RealBox.Contains p r x)
    (hx : 0 ≤ x) (hx2 : x ≤ 1/2) :
    RealBox.Contains p (atanh2 r) (Real.log ((1+x)/(1-x))) := by
  have hh := (series_sound hr 80).2
  have hd := RealBox.add_sound hh hh
  have he : realSeries x 80+realSeries x 80 = SynergyAnalytic.logAtanhPoly 80 x := by
    simp only [realSeries,SynergyAnalytic.logAtanhPoly]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he] at hd
  have hp := RealBox.scale_real_pos p
  have hs : (scale p:ℝ) = (2:ℝ)^128 := by norm_num [scale,p]
  have hl : ((add (series r 80).2 (series r 80).2).lo:ℝ)/(scale p:ℝ) ≤ SynergyAnalytic.logAtanhPoly 80 x :=
    (div_le_iff₀ hp).2 hd.1
  have hu : SynergyAnalytic.logAtanhPoly 80 x ≤ ((add (series r 80).2 (series r 80).2).hi:ℝ)/(scale p:ℝ) :=
    (le_div_iff₀ hp).2 hd.2
  have hb := SynergyAnalytic.log_atanh80_bounds hx hx2 hl hu
  constructor
  · exact (div_le_iff₀ hp).1 hb.1
  · change Real.log ((1+x)/(1-x))*(scale p:ℝ) ≤
      (((add (series r 80).2 (series r 80).2).hi+1:Int):ℝ)
    have heq : (((add (series r 80).2 (series r 80).2).hi:ℝ)/(scale p:ℝ)+1/(2:ℝ)^128)*(scale p:ℝ) =
        ((add (series r 80).2 (series r 80).2).hi:ℝ)+1 := by rw [←hs];field_simp
    have h := mul_le_mul_of_nonneg_right hb.2 hp.le
    rw [heq] at h
    simpa only [Int.cast_add,Int.cast_one] using h

theorem ln2_sound : RealBox.Contains p (atanh2 (literal p 1 3)) (Real.log 2) := by
  have hr : RealBox.Contains p (literal p 1 3) ((1:ℝ)/3) := by
    simpa only [Int.cast_one,Nat.cast_ofNat] using RealBox.literal_sound p 1 3 (by omega)
  have h := atanh2_sound hr (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1:ℝ)/3≤1/2)
  norm_num at h
  exact h

#print axioms series_sound
#print axioms atanh2_sound
#print axioms ln2_sound
end SynergyBasis.Positive
