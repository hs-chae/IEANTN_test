/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FlatPopulationSamples
import ChordQuadrature
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.FlatPopulationPV.Model
open Real MeasureTheory
noncomputable section

def seriesWeight (j : Nat) : ℝ :=
  ((weight j*coefficient j : Nat) : ℝ)/1000000000000000000

def frequency (j : Nat) : ℝ := 2*π*j

theorem trigPolynomial_series (y : ℝ) : trigPolynomial y =
    ∑ j ∈ Finset.range 16, seriesWeight j*cos (frequency j*y) := by
  unfold trigPolynomial seriesWeight frequency
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem series_period :
    (∑ j ∈ Finset.range 16, seriesWeight j*cos (frequency j*1)) =
    ∑ j ∈ Finset.range 16, seriesWeight j*cos (frequency j*0) := by
  apply Finset.sum_congr rfl
  intro j _
  have h : cos (frequency j) = 1 := by
    convert cos_nat_mul_two_pi j using 1 <;> unfold frequency <;> congr 1 <;> ring
  simp [h]

theorem curvature_budget :
    (∑ j ∈ Finset.range 16, |seriesWeight j| * (frequency j)^2) ≤
      80*∑ j ∈ Finset.range 16,
        (j : ℝ)^2*(coefficient j : ℝ)/1000000000000000000 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hp : π^2 ≤ 10 := by nlinarith [pi_pos, pi_lt_d20]
  have hj : 0≤(j : ℝ)^2 := sq_nonneg _
  have hf : (frequency j)^2 ≤ 40*(j : ℝ)^2 := by
    unfold frequency
    nlinarith [mul_le_mul_of_nonneg_right hp hj]
  have hw : (weight j : ℝ) ≤ 2 := by exact_mod_cast weights_fit j
  have ha0 : (0 : ℝ)≤coefficient j := Nat.cast_nonneg _
  have hw0 : (0 : ℝ)≤weight j := Nat.cast_nonneg _
  have hs0 : 0≤seriesWeight j := by unfold seriesWeight; positivity
  have hs : seriesWeight j ≤ 2*(coefficient j : ℝ)/1000000000000000000 := by
    unfold seriesWeight
    push_cast
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hw ha0) (by norm_num)
  rw [abs_of_nonneg hs0]
  calc
    _ ≤ (2*(coefficient j : ℝ)/1000000000000000000)*(40*(j : ℝ)^2) :=
      mul_le_mul hs hf (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- Exact rational check of the conservative global-chord allowance, on the
unchanged input coefficients. This is one finite fact in the matched control. -/
def chordQ : ℚ := (80/(12*256^2)) *
  ∑ j ∈ Finset.range 16, (j : ℚ)^2*(coefficient j : ℚ)/1000000000000000000

theorem chordQ_bound : chordQ ≤ (chordUpper : ℚ)/1000000000000000000 := by
  decide +kernel

theorem chord_real_bound :
    (80*∑ j ∈ Finset.range 16,
      (j : ℝ)^2*(coefficient j : ℝ)/1000000000000000000)/(12*(256 : ℝ)^2) ≤
      (chordUpper : ℝ)/1000000000000000000 := by
  have h : (chordQ : ℝ) ≤ (((chordUpper : ℚ)/1000000000000000000 : ℚ) : ℝ) := by
    exact_mod_cast chordQ_bound
  unfold chordQ at h
  push_cast at h
  convert h using 1 <;> ring

theorem sum_map_range (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem rounded_sample_average :
    (∑ k ∈ Finset.range 256, |trigPolynomial ((k : ℝ)/256)|)/256 ≤
      (((List.range 256).map fun k => (sampleUpper k+255)/256).sum : Nat)/
        (1000000000000000000 : ℝ) := by
  rw [sum_map_range]
  push_cast
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_le_sum
  intro k _
  have he := actual_grid_enclosure k
  have hn : sampleUpper k ≤ ((sampleUpper k+255)/256)*256 := by omega
  have hr : (sampleUpper k : ℝ) ≤ (((sampleUpper k+255)/256 : Nat) : ℝ)*256 := by
    exact_mod_cast hn
  linarith

/-- Mathematical enclosure produced by the source-computed trigonometric grid
and conservative curvature allowance. No inverse-Fourier identity is assumed. -/
theorem periodic_norm_upper :
    (∫ y in (0 : ℝ)..1, |trigPolynomial y|) ≤
      (normUpper : ℝ)/1000000000000000000 := by
  have h := RH080Next.Primal.cosine_series_abs_chord_quadrature 16
    seriesWeight frequency 256 (by decide) series_period
  simp_rw [←trigPolynomial_series] at h
  have hb := div_le_div_of_nonneg_right curvature_budget
    (by positivity : (0 : ℝ)≤12*(256 : ℝ)^2)
  have hc := chord_real_bound
  have hs := rounded_sample_average
  have hn : (normUpper : ℝ) =
      (((List.range 256).map fun k => (sampleUpper k+255)/256).sum : Nat)+
        (chordUpper : ℝ) := by unfold normUpper; push_cast; rfl
  rw [hn]
  linarith

#print axioms periodic_norm_upper
#print axioms chordQ_bound
end
end RH080Next.FlatPopulationPV.Model
