/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080Next.Explicit

def node (nodes : List ℚ) (j : ℕ) : ℝ := (nodes.getD j 0 : ℚ)
def hat (x : ℝ) : ℝ := max 0 (1 - |x|)

/-- Even affine interpolant, with an implicit zero outer node. Concrete inputs
carry the separate check that their final stored node is this zero. -/
def affineSpectrum (nodes : List ℚ) (m : ℕ) (v : ℝ) : ℝ :=
  node nodes 0 * hat ((m : ℝ) * v) +
    ∑ j ∈ Finset.Ico 1 (nodes.length - 1),
      node nodes j * (hat ((m : ℝ) * v - j) + hat ((m : ℝ) * v + j))

def radius (nodes : List ℚ) (m : ℕ) : ℝ := (nodes.length - 1 : ℕ) / (m : ℝ)
def inverseCosine (W : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ v : ℝ, W v * cos (2 * π * u * v)

def nodalF0 (nodes : List ℚ) (m : ℕ) : ℝ :=
  (node nodes 0 + 2 * ∑ j ∈ Finset.Ico 1 (nodes.length - 1), node nodes j) / m
def nodalMassA0 (nodes : List ℚ) (m : ℕ) : ℝ :=
  (|node nodes 0| + 2 * ∑ j ∈ Finset.Ico 1 (nodes.length - 1), |node nodes j|) / m
def nodalV0 (nodes : List ℚ) : ℝ :=
  2 * ∑ j ∈ Finset.range (nodes.length - 1), |node nodes (j+1) - node nodes j|
def nodalV1 (nodes : List ℚ) (m : ℕ) : ℝ :=
  2 * m * (|node nodes 1 - node nodes 0| +
    (∑ j ∈ Finset.Ico 1 (nodes.length - 1),
      |node nodes (j+1) - 2 * node nodes j + node nodes (j-1)|) +
    |node nodes (nodes.length-1) - node nodes (nodes.length-2)|)
def nodalH (nodes : List ℚ) (m : ℕ) : ℝ :=
  max 0 (node nodes m) + ∑ j ∈ Finset.Ico m (nodes.length - 1),
    max 0 (max 0 (node nodes (j+1)) - max 0 (node nodes j))
def nodalMu2Upper (nodes : List ℚ) (m : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (nodes.length - 1),
    ((6 * (j : ℝ)^2 + 4*j + 1) * |node nodes j| +
      (6 * (j : ℝ)^2 + 8*j + 3) * |node nodes (j+1)|)) / (6 * (m : ℝ)^3)

@[fun_prop] theorem continuous_hat : Continuous hat := by unfold hat; fun_prop
@[simp] theorem hat_neg (x : ℝ) : hat (-x) = hat x := by simp [hat]
theorem hat_nonneg (x : ℝ) : 0 ≤ hat x := le_max_left _ _
theorem hat_eq_zero (x : ℝ) (hx : 1 ≤ |x|) : hat x = 0 := by
  exact max_eq_left (by linarith)
theorem hat_le_one (x : ℝ) : hat x ≤ 1 := by
  simp only [hat, max_le_iff]
  exact ⟨by norm_num, by linarith [abs_nonneg x]⟩

@[fun_prop] theorem continuous_affineSpectrum (nodes : List ℚ) (m : ℕ) :
    Continuous (affineSpectrum nodes m) := by
  unfold affineSpectrum
  fun_prop

theorem affineSpectrum_even (nodes : List ℚ) (m : ℕ) :
    Function.Even (affineSpectrum nodes m) := by
  intro v
  unfold affineSpectrum
  rw [show (m : ℝ) * (-v) = -((m : ℝ) * v) by ring, hat_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -((m : ℝ) * v) - (j : ℝ) = -((m : ℝ) * v + j) by ring,
    show -((m : ℝ) * v) + (j : ℝ) = -((m : ℝ) * v - j) by ring,
    hat_neg, hat_neg, add_comm]

theorem affineSpectrum_eq_zero_of_radius_le (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (v : ℝ)
    (hv : radius nodes m ≤ |v|) : affineSpectrum nodes m v = 0 := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hN : (1 : ℝ) ≤ (nodes.length - 1 : ℕ) := by exact_mod_cast (show 1 ≤ nodes.length-1 by omega)
  have ht : ((nodes.length-1 : ℕ) : ℝ) ≤ |(m : ℝ)*v| := by
    rw [abs_mul, abs_of_pos hm']
    have h := (div_le_iff₀ hm').mp hv
    nlinarith
  unfold affineSpectrum
  rw [hat_eq_zero _ (hN.trans ht), mul_zero]
  simp only [zero_add]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' : j + 1 ≤ nodes.length - 1 := by
    have h := (Finset.mem_Ico.mp hj).2
    omega
  have hjr : (j : ℝ) + 1 ≤ (nodes.length - 1 : ℕ) := by exact_mod_cast hj'
  have h1 := abs_sub_abs_le_abs_sub ((m : ℝ)*v) (j : ℝ)
  have h2 := abs_sub_abs_le_abs_sub ((m : ℝ)*v) (-(j : ℝ))
  have hjabs : |(j : ℝ)| = (j : ℝ) := abs_of_nonneg (Nat.cast_nonneg j)
  rw [hjabs] at h1
  rw [abs_neg, hjabs, sub_neg_eq_add] at h2
  rw [hat_eq_zero _ (by linarith), hat_eq_zero _ (by linarith), add_zero, mul_zero]

theorem affineSpectrum_support_subset (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) :
    Function.support (affineSpectrum nodes m) ⊆
      Icc (-radius nodes m) (radius nodes m) := by
  intro v hv
  apply abs_le.mp
  apply le_of_lt
  apply lt_of_not_ge
  intro h
  exact hv (affineSpectrum_eq_zero_of_radius_le nodes m hlen hm v h)

theorem hasCompactSupport_affineSpectrum (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) :
    HasCompactSupport (affineSpectrum nodes m) := by
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (affineSpectrum_support_subset nodes m hlen hm) isClosed_Icc)

theorem integrable_affineSpectrum (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) :
    Integrable (affineSpectrum nodes m) :=
  (continuous_affineSpectrum nodes m).integrable_of_hasCompactSupport
    (hasCompactSupport_affineSpectrum nodes m hlen hm)

end RH080Next.Explicit
