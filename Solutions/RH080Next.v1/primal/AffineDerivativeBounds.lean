/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFiniteDifference
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
namespace RH080Next.Primal
open RH080Next.Explicit

/-- Numerator after two exact discrete integrations by parts. -/
def variationNumerator (nodes : List ℚ) (q : ℝ) : ℝ :=
  node nodes 0-node nodes 1+
    (∑ j ∈ Finset.Ico 1 (nodes.length-1),
      (2*node nodes j-node nodes (j-1)-node nodes (j+1))*cos ((j:ℝ)*q))-
    node nodes (nodes.length-2)*cos ((nodes.length-1:ℕ)*q)

def variationNumeratorDerivative (nodes : List ℚ) (q : ℝ) : ℝ :=
  (∑ j ∈ Finset.Ico 1 (nodes.length-1),
    (2*node nodes j-node nodes (j-1)-node nodes (j+1))*(-sin ((j:ℝ)*q)*(j:ℝ)))-
    node nodes (nodes.length-2)*(-sin ((nodes.length-1:ℕ)*q)*(nodes.length-1:ℕ))

private theorem first_difference_identity (a C : ℕ → ℝ) (N : ℕ) (hN : 1≤N) :
    (∑ j ∈ Finset.range N, (a (j+1)-a j)*(C (j+1)-C j)) =
      (a 0-a 1)*C 0+
        (∑ j ∈ Finset.Ico 1 N, (2*a j-a (j-1)-a (j+1))*C j)+
        (a N-a (N-1))*C N := by
  induction N, hN using Nat.le_induction with
  | base => simp; ring
  | succ N hN ih =>
    rw [Finset.sum_range_succ,Finset.sum_Ico_succ_top hN,ih]
    simp only [Nat.add_sub_cancel]
    ring

/-- First differences expose cancellation near every numerator zero. -/
theorem variationNumerator_first_difference (nodes : List ℚ) (hlen : 2≤nodes.length)
    (hlast : node nodes (nodes.length-1)=0) (q : ℝ) :
    variationNumerator nodes q =
      ∑ j ∈ Finset.range (nodes.length-1),
        (node nodes (j+1)-node nodes j)*(cos ((j+1:ℕ)*q)-cos ((j:ℝ)*q)) := by
  have h := first_difference_identity (node nodes) (fun j => cos ((j:ℝ)*q))
    (nodes.length-1) (by omega)
  rw [hlast] at h
  simpa [variationNumerator,sub_eq_add_neg,show nodes.length-1-1=nodes.length-2 by omega] using h.symm

/-- The variation bound is linear in the true phase, rather than a large
coefficient-wise bound with lost cancellation. -/
theorem variationNumerator_abs_le_first_variation (nodes : List ℚ)
    (hlen : 2≤nodes.length) (hlast : node nodes (nodes.length-1)=0) (q : ℝ) :
    |variationNumerator nodes q| ≤ |q| * nodalV0 nodes/2 := by
  rw [variationNumerator_first_difference nodes hlen hlast]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ j ∈ Finset.range (nodes.length-1),
      |(node nodes (j+1)-node nodes j)*(cos ((j+1:ℕ)*q)-cos ((j:ℝ)*q))|) ≤
        ∑ j ∈ Finset.range (nodes.length-1), |node nodes (j+1)-node nodes j| * |q| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_sub_cancel_left] using
        Real.abs_cos_sub_cos_le (((j+1:ℕ):ℝ)*q) ((j:ℝ)*q)
    _ = |q| * nodalV0 nodes/2 := by rw [← Finset.sum_mul]; unfold nodalV0; ring

/-- Differentiation of the finite genuine cosine numerator is entirely analytic. -/
theorem hasDerivAt_variationNumerator (nodes : List ℚ) (q : ℝ) :
    HasDerivAt (variationNumerator nodes) (variationNumeratorDerivative nodes q) q := by
  have hterm (j : ℕ) :
      HasDerivAt (fun z : ℝ =>
        (2*node nodes j-node nodes (j-1)-node nodes (j+1))*cos ((j:ℝ)*z))
        ((2*node nodes j-node nodes (j-1)-node nodes (j+1))*(-sin ((j:ℝ)*q)*(j:ℝ))) q := by
    simpa using (((hasDerivAt_id q).const_mul (j:ℝ)).cos.const_mul
      (2*node nodes j-node nodes (j-1)-node nodes (j+1)))
  have hs : HasDerivAt (fun z : ℝ =>
      ∑ j ∈ Finset.Ico 1 (nodes.length-1),
        (2*node nodes j-node nodes (j-1)-node nodes (j+1))*cos ((j:ℝ)*z))
      (∑ j ∈ Finset.Ico 1 (nodes.length-1),
        (2*node nodes j-node nodes (j-1)-node nodes (j+1))*(-sin ((j:ℝ)*q)*(j:ℝ))) q :=
    HasDerivAt.fun_sum (u := Finset.Ico 1 (nodes.length-1)) (fun j hj => hterm j)
  have he : HasDerivAt (fun z : ℝ =>
      node nodes (nodes.length-2)*cos (((nodes.length-1:ℕ):ℝ)*z))
      (node nodes (nodes.length-2)*(-sin (((nodes.length-1:ℕ):ℝ)*q)*((nodes.length-1:ℕ):ℝ))) q := by
    simpa using (((hasDerivAt_id q).const_mul ((nodes.length-1:ℕ):ℝ)).cos.const_mul
      (node nodes (nodes.length-2)))
  unfold variationNumerator variationNumeratorDerivative
  convert! ((hasDerivAt_const q (node nodes 0-node nodes 1)).add hs).sub he using 1
  simp only [zero_add]

def variationMass (nodes : List ℚ) : ℝ :=
  |node nodes 1-node nodes 0|+
    (∑ j ∈ Finset.Ico 1 (nodes.length-1),
      |node nodes (j+1)-2*node nodes j+node nodes (j-1)|)+
    |node nodes (nodes.length-1)-node nodes (nodes.length-2)|

theorem nodalV1_eq_variationMass (nodes : List ℚ) (m : ℕ) :
    nodalV1 nodes m=2*(m:ℝ)*variationMass nodes := rfl

private theorem abs_coefficient_sine_frequency (a t j N : ℝ)
    (hj : 0≤j) (hN : j≤N) : |a*(-sin t*j)|≤N*|a| := by
  rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg hj]
  calc
    |a| * (|sin t| * j) ≤ |a| * (1*j) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) hj) (abs_nonneg a)
    _ ≤ |a| * N := by simpa using mul_le_mul_of_nonneg_left hN (abs_nonneg a)
    _ = N*|a| := by ring

/-- The derivative of the cancellation-preserving numerator uses only the
second variation, weighted by the actual support radius. -/
theorem variationNumeratorDerivative_abs_le (nodes : List ℚ)
    (hlast : node nodes (nodes.length-1)=0) (q : ℝ) :
    |variationNumeratorDerivative nodes q|≤(nodes.length-1:ℕ)*variationMass nodes := by
  unfold variationNumeratorDerivative
  apply (abs_sub _ _).trans
  have hs : |∑ j ∈ Finset.Ico 1 (nodes.length-1),
      (2*node nodes j-node nodes (j-1)-node nodes (j+1))*(-sin ((j:ℝ)*q)*(j:ℝ))|≤
      (nodes.length-1:ℕ)*∑ j ∈ Finset.Ico 1 (nodes.length-1),
        |node nodes (j+1)-2*node nodes j+node nodes (j-1)| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjN : (j:ℝ)≤((nodes.length-1:ℕ):ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hj).2.le
    have h := abs_coefficient_sine_frequency
      (2*node nodes j-node nodes (j-1)-node nodes (j+1)) ((j:ℝ)*q)
      j (nodes.length-1:ℕ) (Nat.cast_nonneg j) hjN
    simpa only [show 2*node nodes j-node nodes (j-1)-node nodes (j+1)=
      -(node nodes (j+1)-2*node nodes j+node nodes (j-1)) by ring,abs_neg] using h
  have he := abs_coefficient_sine_frequency (node nodes (nodes.length-2))
    (((nodes.length-1:ℕ):ℝ)*q) (nodes.length-1:ℕ) (nodes.length-1:ℕ)
    (Nat.cast_nonneg _) le_rfl
  have hlastabs : |node nodes (nodes.length-2)|=
      |node nodes (nodes.length-1)-node nodes (nodes.length-2)| := by rw [hlast,zero_sub,abs_neg]
  rw [hlastabs] at he
  have hN : (0:ℝ)≤((nodes.length-1:ℕ):ℝ) := Nat.cast_nonneg _
  unfold variationMass
  nlinarith [abs_nonneg (node nodes 1-node nodes 0)]

/-- The actual Fourier integral, not an assumed scalar certificate, equals the
cancellation-preserving expression away from zero. -/
theorem inverseCosine_eq_variationNumerator (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m)
    (hlast : node nodes (nodes.length-1)=0) (u : ℝ) (hu : u≠0) :
    inverseCosine (affineSpectrum nodes m) u =
      ((m:ℝ)/(2*π^2))*(variationNumerator nodes (2*π*u/(m:ℝ))/u^2) := by
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hq : 2*π*u/(m:ℝ)≠0 := div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hu) hm0
  have hnum := nodalPolynomial_second_difference nodes hlen hlast (u/(m:ℝ))
  have hphase (j : ℕ) : 2*π*j*(u/(m:ℝ))=(j:ℝ)*(2*π*u/(m:ℝ)) := by ring
  simp_rw [hphase] at hnum
  rw [show 2*π*(u/(m:ℝ))=2*π*u/(m:ℝ) by ring] at hnum
  change (1-cos (2*π*u/(m:ℝ)))*nodalPolynomial nodes (u/(m:ℝ))=
    variationNumerator nodes (2*π*u/(m:ℝ)) at hnum
  rw [inverseCosine_affineSpectrum nodes m hm,integral_hat_mul_cos _ hq]
  calc
    _ = ((m:ℝ)/(2*π^2))*
        (((1-cos (2*π*u/(m:ℝ)))*nodalPolynomial nodes (u/(m:ℝ)))/u^2) := by
      field_simp
      <;> ring
    _ = _ := by rw [hnum]

def affineInverseDerivative (nodes : List ℚ) (m : ℕ) (u : ℝ) : ℝ :=
  ((m:ℝ)/(2*π^2))*(
    variationNumeratorDerivative nodes (2*π*u/(m:ℝ))*(2*π/(m:ℝ))/u^2-
      2*variationNumerator nodes (2*π*u/(m:ℝ))/u^3)

/-- Actual derivative, including the quotient's cancellation term. -/
theorem hasDerivAt_inverseCosine_affineSpectrum_ne_zero (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m)
    (hlast : node nodes (nodes.length-1)=0) (u : ℝ) (hu : u≠0) :
    HasDerivAt (inverseCosine (affineSpectrum nodes m))
      (affineInverseDerivative nodes m u) u := by
  have hs := (hasDerivAt_variationNumerator nodes (2*π*u/(m:ℝ))).comp u
    (((hasDerivAt_id u).const_mul (2*π)).div_const (m:ℝ))
  have h := (hs.div ((hasDerivAt_id u).pow 2) (pow_ne_zero 2 hu)).const_mul
    ((m:ℝ)/(2*π^2))
  have hd : HasDerivAt (fun v : ℝ =>
      ((m:ℝ)/(2*π^2))*(variationNumerator nodes (2*π*v/(m:ℝ))/v^2))
      (affineInverseDerivative nodes m u) u := by
    convert! h using 1
    unfold affineInverseDerivative
    simp only [id_eq,mul_one,Function.comp_def,Pi.pow_apply,Nat.reduceSub,pow_one]
    field_simp [hu]
    <;> ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hu] with v hv
  exact inverseCosine_eq_variationNumerator nodes m hlen hm hlast v hv

/-- Sharp tail envelope required by the zero-count error integral. All endpoint
slope jumps are included in V1; V0 controls the quotient cancellation term. -/
theorem affineInverseDerivative_abs_le (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m)
    (hlast : node nodes (nodes.length-1)=0) (u : ℝ) (hu : u≠0) :
    |affineInverseDerivative nodes m u|≤
      (radius nodes m*nodalV1 nodes m+2*nodalV0 nodes)/(2*π*u^2) := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hm0 := hm'.ne'
  have hf : (0:ℝ)<2*π/(m:ℝ) := by positivity
  have hu2 : 0<u^2 := sq_pos_of_ne_zero hu
  have hua : |u|≠0 := abs_ne_zero.mpr hu
  have hqabs : |2*π*u/(m:ℝ)|=2*π*|u|/(m:ℝ) := by
    rw [abs_div,abs_mul,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos hm']
    norm_num
  have hS := variationNumerator_abs_le_first_variation nodes hlen hlast (2*π*u/(m:ℝ))
  rw [hqabs] at hS
  have hD := variationNumeratorDerivative_abs_le nodes hlast (2*π*u/(m:ℝ))
  have hA : |variationNumeratorDerivative nodes (2*π*u/(m:ℝ))*(2*π/(m:ℝ))/u^2|≤
      ((nodes.length-1:ℕ):ℝ)*variationMass nodes*(2*π/(m:ℝ))/u^2 := by
    rw [abs_div,abs_mul,abs_of_pos hf,abs_of_pos hu2]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hD hf.le) hu2.le
  have hB : |2*variationNumerator nodes (2*π*u/(m:ℝ))/u^3|≤
      (2*π/(m:ℝ))*nodalV0 nodes/u^2 := by
    calc
      _ = 2*|variationNumerator nodes (2*π*u/(m:ℝ))|/|u|^3 := by
        rw [abs_div,abs_mul,abs_pow]; norm_num
      _ ≤ 2*(2*π*|u|/(m:ℝ)*nodalV0 nodes/2)/|u|^3 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS (by norm_num))
          (by positivity)
      _ = _ := by
        rw [← sq_abs u]
        field_simp [hua,hm0]
        <;> ring
  unfold affineInverseDerivative
  rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(m:ℝ)/(2*π^2))]
  apply (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hA hB))
    (by positivity : (0:ℝ)≤(m:ℝ)/(2*π^2))).trans
  apply le_of_eq
  rw [nodalV1_eq_variationMass]
  unfold radius
  field_simp [hm0,Real.pi_ne_zero,hu]
  <;> ring

/-- The bound applies to mathlib's actual derivative of the actual Fourier
integral, rather than to a separately supplied derivative function. -/
theorem deriv_inverseCosine_affineSpectrum_abs_le (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m)
    (hlast : node nodes (nodes.length-1)=0) (u : ℝ) (hu : u≠0) :
    |deriv (inverseCosine (affineSpectrum nodes m)) u|≤
      (radius nodes m*nodalV1 nodes m+2*nodalV0 nodes)/(2*π*u^2) := by
  rw [(hasDerivAt_inverseCosine_affineSpectrum_ne_zero nodes m hlen hm hlast u hu).deriv]
  exact affineInverseDerivative_abs_le nodes m hlen hm hlast u hu

#print axioms variationNumerator_first_difference
#print axioms variationNumerator_abs_le_first_variation
#print axioms hasDerivAt_variationNumerator
#print axioms variationNumeratorDerivative_abs_le
#print axioms inverseCosine_eq_variationNumerator
#print axioms hasDerivAt_inverseCosine_affineSpectrum_ne_zero
#print axioms affineInverseDerivative_abs_le
#print axioms deriv_inverseCosine_affineSpectrum_abs_le
end RH080Next.Primal
