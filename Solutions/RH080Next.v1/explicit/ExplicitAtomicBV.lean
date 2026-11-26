/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitDiscreteBV
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
namespace RH080Next.Explicit
variable {ι : Type*} [DecidableEq ι]

def atomicPrefix (P : Finset ι) (x w : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ p ∈ P, if x p ≤ t then w p else 0

def unitCell (x : ℝ) (n : ℕ) : ℕ := ⌈x*(n:ℝ)⌉₊-1

theorem unitCell_spec (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    unitCell x n < n ∧ (unitCell x n:ℝ)/n < x ∧ x ≤ ((unitCell x n:ℝ)+1)/n := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hr : 0 < x*(n:ℝ) := mul_pos hx hnr
  have hcp : 1 ≤ ⌈x*(n:ℝ)⌉₊ := Nat.one_le_ceil_iff.mpr hr
  have hcu : ⌈x*(n:ℝ)⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hs := (Nat.ceil_eq_iff (show ⌈x*(n:ℝ)⌉₊≠0 by omega)).mp rfl
  have he : unitCell x n+1=⌈x*(n:ℝ)⌉₊ := by dsimp [unitCell]; omega
  refine ⟨by dsimp [unitCell]; omega,?_,?_⟩
  · exact (div_lt_iff₀ hnr).mpr hs.1
  · apply (le_div_iff₀ hnr).mpr
    have hcast : (⌈x*(n:ℝ)⌉₊:ℝ)=(unitCell x n:ℝ)+1 := by exact_mod_cast he.symm
    rw [hcast] at hs
    exact hs.2

theorem unitCell_membership (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i : ℕ) : ((i:ℝ)/n < x ∧ x ≤ ((i:ℝ)+1)/n) ↔ i=unitCell x n := by
  have hs := unitCell_spec n hn x hx hx1
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  constructor
  · intro hi
    have h1 := (div_lt_iff₀ hnr).mp hi.1
    have h2 := (le_div_iff₀ hnr).mp hi.2
    have h3 := (div_lt_iff₀ hnr).mp hs.2.1
    have h4 := (le_div_iff₀ hnr).mp hs.2.2
    have hi' : i < unitCell x n+1 := by exact_mod_cast (by linarith : (i:ℝ) < (unitCell x n:ℝ)+1)
    have hj' : unitCell x n < i+1 := by exact_mod_cast (by linarith : (unitCell x n:ℝ) < (i:ℝ)+1)
    omega
  · rintro rfl
    exact hs.2

theorem atomicPrefix_sub (P : Finset ι) (x w : ι → ℝ) (a b : ℝ) (hab : a ≤ b) :
    atomicPrefix P x w b-atomicPrefix P x w a=
      ∑ p ∈ P, if a < x p ∧ x p ≤ b then w p else 0 := by
  unfold atomicPrefix
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hl : x p ≤ a
  · have hr := hl.trans hab
    simp [hl,hr,not_lt.mpr hl]
  · have hl' : a < x p := lt_of_not_ge hl
    by_cases hr : x p ≤ b <;> simp [hl,hl',hr]

def atomicGridSum (P : Finset ι) (x w : ι → ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, f ((i:ℝ)/n)*
    (atomicPrefix P x w (((i:ℝ)+1)/n)-atomicPrefix P x w ((i:ℝ)/n))

theorem atomicGridSum_eq (P : Finset ι) (x w : ι → ℝ) (f : ℝ → ℝ)
    (n : ℕ) (hn : 0 < n) (hx : ∀ p∈P, 0 < x p ∧ x p ≤ 1) :
    atomicGridSum P x w f n=∑ p ∈ P, w p*f ((unitCell (x p) n:ℝ)/n) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  unfold atomicGridSum
  have hcell (i : ℕ) := atomicPrefix_sub P x w ((i:ℝ)/n) (((i:ℝ)+1)/n)
    (div_le_div_of_nonneg_right (by linarith : (i:ℝ) ≤ (i:ℝ)+1) hnr.le)
  simp_rw [hcell]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hxp := hx p hp
  simp_rw [unitCell_membership n hn (x p) hxp.1 hxp.2]
  simp [mul_ite,Finset.mem_range.mpr (unitCell_spec n hn (x p) hxp.1 hxp.2).1,mul_comm]

theorem atomicGridSum_approx (P : Finset ι) (x w : ι → ℝ) (f : ℝ → ℝ)
    (n : ℕ) (hn : 0 < n) (L : ℝ) (hL : 0 ≤ L)
    (hx : ∀ p∈P, 0 < x p ∧ x p ≤ 1) (hw : ∀ p∈P, 0 ≤ w p)
    (hLip : ∀ a∈Icc (0:ℝ) 1, ∀ b∈Icc (0:ℝ) 1, |f a-f b| ≤ L*|a-b|) :
    (∑ p ∈ P, w p*f (x p))  ≤  atomicGridSum P x w f n+(L/n)*(∑ p ∈ P, w p) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  rw [atomicGridSum_eq P x w f n hn hx,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hs := unitCell_spec n hn (x p) (hx p hp).1 (hx p hp).2
  have hleft : (unitCell (x p) n:ℝ)/n∈Icc (0:ℝ) 1 := ⟨by positivity,hs.2.1.le.trans (hx p hp).2⟩
  have hd : |x p-(unitCell (x p) n:ℝ)/n| ≤ 1/n := by
    rw [abs_of_nonneg (by linarith [hs.2.1])]
    have he : ((unitCell (x p) n:ℝ)+1)/n=(unitCell (x p) n:ℝ)/n+1/n := by ring
    rw [he] at hs
    linarith [hs.2.2]
  have hl := hLip (x p) ⟨(hx p hp).1.le,(hx p hp).2⟩ _ hleft
  have hm := mul_le_mul_of_nonneg_left hd hL
  have hf : f (x p) ≤ f ((unitCell (x p) n:ℝ)/n)+L/n := by
    have hh := le_abs_self (f (x p)-f ((unitCell (x p) n:ℝ)/n))
    have he : L*(1/(n:ℝ))=L/n := by ring
    rw [he] at hm
    linarith
  have h := mul_le_mul_of_nonneg_left hf (hw p hp)
  nlinarith

theorem uniform_left_quadrature_le (f : ℝ → ℝ) (hf : Continuous f)
    (n : ℕ) (hn : 0 < n) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ a∈Icc (0:ℝ) 1, ∀ b∈Icc (0:ℝ) 1, |f a-f b| ≤ L*|a-b|) :
    (∑ i ∈ Finset.range n, f ((i:ℝ)/n))/(n:ℝ) ≤
      (∫ t in (0:ℝ)..1, f t)+L/n := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hn0 : (n:ℝ)≠0 := hnr.ne'
  have hcell (i : ℕ) (hi : i < n) :
      f ((i:ℝ)/n)/n-L/(n:ℝ)^2 ≤
        ∫ t in ((i:ℝ)/n)..(((i:ℝ)+1)/n), f t := by
    have hil : (0:ℝ) ≤ (i:ℝ)/n := by positivity
    have hiu : ((i:ℝ)+1)/n ≤ 1 := by
      apply (div_le_one hnr).mpr
      exact_mod_cast (show i+1 ≤ n by omega)
    have hab : (i:ℝ)/n ≤ ((i:ℝ)+1)/n :=
      div_le_div_of_nonneg_right (by linarith) hnr.le
    have hpoint (t : ℝ) (ht : t∈Icc ((i:ℝ)/n) (((i:ℝ)+1)/n)) :
        f ((i:ℝ)/n)-L/n ≤ f t := by
      have hd : |(i:ℝ)/n-t| ≤ 1/n := by
        rw [abs_of_nonpos (by linarith [ht.1])]
        have he : ((i:ℝ)+1)/n=(i:ℝ)/n+1/n := by ring
        rw [he] at ht
        linarith [ht.2]
      have h := hLip ((i:ℝ)/n) ⟨hil,hab.trans hiu⟩ t ⟨hil.trans ht.1,ht.2.trans hiu⟩
      have hm := mul_le_mul_of_nonneg_left hd hL
      have hh := le_abs_self (f ((i:ℝ)/n)-f t)
      have he : L*(1/(n:ℝ))=L/n := by ring
      rw [he] at hm
      linarith
    have h := intervalIntegral.integral_mono_on hab
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f ((i:ℝ)/n)-L/n) volume _ _)
      (hf.intervalIntegrable _ _) hpoint
    rw [intervalIntegral.integral_const,smul_eq_mul] at h
    convert h using 1 <;> field_simp <;> ring
  have hsum := Finset.sum_le_sum (fun i hi => hcell i (Finset.mem_range.mp hi))
  have hp := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := f) (a := fun i : ℕ => (i:ℝ)/n) (n := n)
    (fun i hi => hf.intervalIntegrable _ _)
  simp only [Nat.cast_add,Nat.cast_one] at hp
  rw [hp] at hsum
  simp only [Nat.cast_zero,zero_div,div_self hn0] at hsum
  have he : (∑ i ∈ Finset.range n, (f ((i:ℝ)/n)/n-L/(n:ℝ)^2))=
      (∑ i ∈ Finset.range n, f ((i:ℝ)/n))/(n:ℝ)-L/n := by
    rw [Finset.sum_sub_distrib,←Finset.sum_div,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    field_simp
  rw [he] at hsum
  linarith

theorem atomicGridSum_BV_le (P : Finset ι) (x w : ι → ℝ) (f : ℝ → ℝ)
    (n : ℕ) (hn : 0 < n) (B C H : ℝ) (hC : 0 ≤ C)
    (hf : ∀ t∈Icc (0:ℝ) 1, 0 ≤ f t)
    (hcount : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      atomicPrefix P x w b-atomicPrefix P x w a ≤ B*(b-a)+C)
    (hvar : f 0+∑ i ∈ Finset.range n,
      max 0 (f (((i:ℝ)+1)/n)-f ((i:ℝ)/n)) ≤ H) :
    atomicGridSum P x w f n ≤
      (B/n)*(∑ i ∈ Finset.range n, f ((i:ℝ)/n))+C*H := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  let S : ℕ → ℝ := fun i => atomicPrefix P x w ((i:ℝ)/n)-B*((i:ℝ)/n)
  let F : ℕ → ℝ := fun i => f ((i:ℝ)/n)
  have hF (i : ℕ) (hi : i ≤ n) : 0 ≤ F i :=
    hf _ ⟨by positivity,(div_le_one hnr).mpr (by exact_mod_cast hi)⟩
  have hI (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) : S j-S i ≤ C := by
    have h := hcount ((i:ℝ)/n) ((j:ℝ)/n) (by positivity)
      (div_le_div_of_nonneg_right (by exact_mod_cast hij) hnr.le)
      ((div_le_one hnr).mpr (by exact_mod_cast hj))
    dsimp [S]
    nlinarith
  have h := finite_interval_positive_variation_bound S F n C hC hF hI
  have hvar' : F 0+∑ i ∈ Finset.range n, max 0 (F (i+1)-F i) ≤ H := by
    simpa only [F,Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_div] using hvar
  have hv := mul_le_mul_of_nonneg_left hvar' hC
  have he : (∑ i ∈ Finset.range n, F i*(S (i+1)-S i))=
      atomicGridSum P x w f n-(B/n)*(∑ i ∈ Finset.range n, f ((i:ℝ)/n)) := by
    unfold atomicGridSum
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [F,S]
    push_cast
    ring
  rw [he] at h
  linarith

/-- A genuine continuum inequality for a finite atomic measure, derived from
all interval-count bounds. The only variation condition is on successively
refined grids; the affine-window lemma proves it exactly from actual nodes.
No merged-component oracle, quadrature certificate or numerical premise is
used. Both finite-atom transport and the continuous integral error vanish
by the proved Lipschitz estimates. -/
theorem finite_atomic_continuous_BV_bound
    (P : Finset ι) (x w : ι → ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (D : ℕ) (hD : 0 < D) (B C H L : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hx : ∀ p∈P, 0 < x p ∧ x p ≤ 1) (hw : ∀ p∈P, 0 ≤ w p)
    (hfn : ∀ t∈Icc (0:ℝ) 1, 0 ≤ f t)
    (hLip : ∀ a∈Icc (0:ℝ) 1, ∀ b∈Icc (0:ℝ) 1, |f a-f b| ≤ L*|a-b|)
    (hcount : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      atomicPrefix P x w b-atomicPrefix P x w a ≤ B*(b-a)+C)
    (hvar : ∀ G : ℕ, 0 < G →
      f 0+∑ i ∈ Finset.range (D*G),
        max 0 (f (((i:ℝ)+1)/(D*G:ℕ))-f ((i:ℝ)/(D*G:ℕ))) ≤ H) :
    (∑ p ∈ P, w p*f (x p)) ≤ B*(∫ t in (0:ℝ)..1, f t)+C*H := by
  have hW : 0 ≤ ∑ p ∈ P, w p := Finset.sum_nonneg (fun p hp => hw p hp)
  let K : ℝ := L*(B+∑ p ∈ P, w p)
  have hK : 0 ≤ K := mul_nonneg hL (add_nonneg hB hW)
  have hbound (G : ℕ) (hG : 0 < G) :
      (∑ p ∈ P, w p*f (x p)) ≤ B*(∫ t in (0:ℝ)..1, f t)+C*H+K/(D*G:ℕ) := by
    have hn : 0 < D*G := Nat.mul_pos hD hG
    have ha := atomicGridSum_approx P x w f (D*G) hn L hL hx hw hLip
    have hb := atomicGridSum_BV_le P x w f (D*G) hn B C H hC hfn hcount (hvar G hG)
    have hc := uniform_left_quadrature_le f hf (D*G) hn L hL hLip
    have hm := mul_le_mul_of_nonneg_left hc hB
    have he : (B/(D*G:ℕ))*(∑ i ∈ Finset.range (D*G), f ((i:ℝ)/(D*G:ℕ)))=
        B*((∑ i ∈ Finset.range (D*G), f ((i:ℝ)/(D*G:ℕ)))/(D*G:ℕ)) := by ring
    rw [he] at hb
    dsimp [K]
    have he' : L*(B+∑ p ∈ P, w p)/(D*G:ℕ)=
        B*(L/(D*G:ℕ))+(L/(D*G:ℕ))*(∑ p ∈ P, w p) := by ring
    rw [he']
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨G,hGbig⟩ := exists_nat_gt (K/ε+1)
  have hG : 0 < G := by
    have hk0 : 0 ≤ K/ε := div_nonneg hK hε.le
    have hgr : (0:ℝ) < G := by linarith
    exact_mod_cast hgr
  have hDG : (G:ℝ) ≤ (D*G:ℕ) := by
    exact_mod_cast (show G ≤ D*G by nlinarith [show 1 ≤ D by omega])
  have herr : K/(D*G:ℕ) ≤ ε := by
    apply (div_le_iff₀ (show (0:ℝ) < (D*G:ℕ) by exact_mod_cast Nat.mul_pos hD hG)).mpr
    have h := (div_lt_iff₀ hε).mp (show K/ε < (G:ℝ) by linarith)
    nlinarith
  exact (hbound G hG).trans (by linarith)

#print axioms unitCell_spec
#print axioms atomicGridSum_eq
#print axioms atomicGridSum_approx
#print axioms uniform_left_quadrature_le
#print axioms atomicGridSum_BV_le
#print axioms finite_atomic_continuous_BV_bound
end RH080Next.Explicit
