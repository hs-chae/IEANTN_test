/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SourceInterfaces
namespace NicolasContinuation
open Real Finset MertensPositive

/-- Nicolas(2012), Eq(1.3), exact analytic constant, not an inserted decimal. -/
noncomputable def beta : ℝ :=
  2+Real.eulerMascheroniConstant-Real.log Real.pi-2*Real.log 2

noncomputable def product (x : ℝ) : ℝ :=
  ∏ p ∈ primes x, (1-1/(p:ℝ))⁻¹

/-- The actual source's f, Eq(1.9). -/
noncomputable def f (x : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log (Chebyshev.theta x) *
    ∏ p ∈ primes x, (1-1/(p:ℝ))

/-- All nontrivial zeros, with the source's multiplicity convention. -/
def Zero := {s : ℂ // 0<s.re ∧ s.re<1 ∧ riemannZeta s=0}
noncomputable def multiplicity (s : Zero) : ℕ :=
  ((meromorphicOrderAt riemannZeta s.val).untopD 0).toNat
/-- Nicolas Eq(1.18), ordinary positive real x and conjugate-paired real part. -/
noncomputable def spectralTerm (x : ℝ) (s : Zero) : ℂ :=
  (multiplicity s:ℂ) * (x:ℂ)^(Complex.I*(s.val.im:ℂ)) / (s.val*(1-s.val))
noncomputable def W (x : ℝ) : ℝ := (∑' s : Zero,spectralTerm x s).re

/-- Exact literature input, Nicolas Eq(1.19), using the actual spectral function. -/
def SourceNicolas119 : Prop := RiemannHypothesis → ∀ x:ℝ, 1<x →
  Summable (spectralTerm x) ∧ |W x|≤beta
/-- Exact full function in Nicolas's proof Eq(2.19), rather than the rounded
Proposition2.1 upper allowance2.062. Strict599<x is a conservative source subdomain. -/
def SourceNicolas219 : Prop := RiemannHypothesis → ∀ x:ℝ, 599<x →
  Real.log (f x) ≤ -(W x+2)/(Real.sqrt x*Real.log x) +
    (2+beta)/(Real.sqrt x*(Real.log x)^2) +
    4*beta/(Real.sqrt x*(Real.log x)^3) + 1/(2*(x-1))

noncomputable def profile (x : ℝ) : ℝ :=
  2-beta-(2+beta)/Real.log x-4*beta/(Real.log x)^2-
    Real.sqrt x*Real.log x/(2*(x-1))

/-- Positivity of the finite source product is proved for actual prime bases. -/
theorem raw_product_pos (x : ℝ) : 0 < ∏ p ∈ primes x, (1-1/(p:ℝ)) := by
  apply Finset.prod_pos
  intro p hp
  have hpP : p.Prime := (Finset.mem_filter.mp hp).2
  have hp1 : (1:ℝ)<p := by exact_mod_cast hpP.one_lt
  have hdiv : 1/(p:ℝ)<1 := (div_lt_one (by linarith)).mpr hp1
  linarith

theorem product_pos (x : ℝ) : 0<product x := by
  unfold product
  rw [Finset.prod_inv_distrib]
  exact inv_pos.mpr (raw_product_pos x)

theorem theta_gt_one {x : ℝ} (hx : 3≤x) : 1<Chebyshev.theta x := by
  have h3 : Chebyshev.theta 3=Real.log 2+Real.log 3 := by
    have hset : ((Finset.Ioc 0 3).filter Nat.Prime) = ({2,3}:Finset ℕ) := by decide
    unfold Chebyshev.theta
    norm_num only [Nat.floor_ofNat]
    rw [hset]
    norm_num
  have hlow : 1<Chebyshev.theta 3 := by
    rw [h3]
    linarith [Real.log_two_gt_d9,Real.log_three_gt_d9]
  exact hlow.trans_le (Chebyshev.theta_mono hx)

/-- Exact f-to-log-product normalization, with every positivity guard proved. -/
theorem log_ratio_eq {x : ℝ} (hx : 3≤x) :
    Real.log (product x/(Real.exp Real.eulerMascheroniConstant*
      Real.log (Chebyshev.theta x))) = -Real.log (f x) := by
  have htheta := theta_gt_one hx
  have hpos : 0<Real.exp Real.eulerMascheroniConstant*Real.log (Chebyshev.theta x) :=
    mul_pos (Real.exp_pos _) (Real.log_pos htheta)
  have hraw : (∏ p ∈ primes x, (1-1/(p:ℝ))) ≠ 0 := (raw_product_pos x).ne'
  have heq : product x/(Real.exp Real.eulerMascheroniConstant*
      Real.log (Chebyshev.theta x)) = (f x)⁻¹ := by
    unfold product f
    rw [Finset.prod_inv_distrib]
    field_simp [hraw,hpos.ne']
  rw [heq,Real.log_inv]

/-- The complete source function is installed on the actual product observable.
This is a proved transport of named literature inputs, not a new numerical record. -/
theorem log_product_lower
    (h119 : SourceNicolas119) (h219 : SourceNicolas219) (hRH : RiemannHypothesis)
    {x:ℝ} (hx : 599<x) :
    profile x/(Real.sqrt x*Real.log x) ≤
      Real.log (product x/(Real.exp Real.eulerMascheroniConstant*
        Real.log (Chebyshev.theta x))) := by
  have hx0 : 0<x := by linarith
  have hL : 0<Real.log x := Real.log_pos (by linarith)
  have hy : 0<Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hW := (abs_le.mp (h119 hRH x (by linarith)).2).1
  have hs := h219 hRH x hx
  have hd : (2-beta)/(Real.sqrt x*Real.log x) ≤
      (W x+2)/(Real.sqrt x*Real.log x) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  rw [log_ratio_eq (by linarith)]
  have he : profile x/(Real.sqrt x*Real.log x) =
      (2-beta)/(Real.sqrt x*Real.log x) -
      (2+beta)/(Real.sqrt x*(Real.log x)^2) -
      4*beta/(Real.sqrt x*(Real.log x)^3) - 1/(2*(x-1)) := by
    dsimp [profile]
    field_simp [ne_of_gt hy,ne_of_gt hL] <;> ring
  rw [he]
  simp only [neg_div] at hs
  linarith only [hs,hd]

/-- Actual relative-product consumer; log and multiplicative errors are not conflated. -/
theorem relative_product_lower
    (h119 : SourceNicolas119) (h219 : SourceNicolas219) (hRH : RiemannHypothesis)
    {x:ℝ} (hx : 599<x) :
    profile x/(Real.sqrt x*Real.log x) ≤
      product x/(Real.exp Real.eulerMascheroniConstant*
        Real.log (Chebyshev.theta x))-1 := by
  have hpos : 0<product x/(Real.exp Real.eulerMascheroniConstant*
      Real.log (Chebyshev.theta x)) := by
    exact div_pos (product_pos x) (mul_pos (Real.exp_pos _)
      (Real.log_pos (theta_gt_one (by linarith))))
  exact (log_product_lower h119 h219 hRH hx).trans (Real.log_le_sub_one_of_pos hpos)

#print axioms log_product_lower
#print axioms relative_product_lower
end NicolasContinuation
