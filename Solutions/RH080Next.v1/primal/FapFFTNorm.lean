/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FapFFTNodes
import FapFFTCertifiedSamples
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
noncomputable section
open scoped BigOperators Interval
open Real MeasureTheory
namespace RH080Next.Primal.FapFFTKernel
open RH080Next.FFT RH080Next.FFT.IntegerModel RH080Next.Explicit

private theorem foldl_index_sum {α : Type} (xs : List α) (f : α → Nat) (default : α) (acc : Nat) :
    xs.foldl (fun a z => a+f z) acc = acc+∑k ∈ Finset.range xs.length, f (xs.getD k default) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl_cons, ih, Finset.sum_range_succ', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Actual list values, not an assumption about their average or a stored
answer: the trace's absolute-real-part sum is exactly its integer accumulator. -/
theorem sum_decoded_real_abs (xs : List CInt) (n : Nat) (hlen : xs.length = n) :
    (∑k ∈ Finset.range n, |(decode (xs.getD k (0,0))).re|) =
      ((xs.foldl (fun a z => a+z.1.natAbs) 0 : Nat):ℝ)/(unit:ℝ) := by
  have hs := foldl_index_sum xs (fun z : CInt => z.1.natAbs) (0,0) 0
  simp only [zero_add] at hs
  rw [hs, hlen]
  push_cast
  change (∑k ∈ Finset.range n, |((xs.getD k (0,0)).1:ℝ)/(unit:ℝ)|) = _
  simp only [abs_div, abs_of_pos (by norm_num [unit] : (0:ℝ)<(unit:ℝ)), ← natAbs_cast]
  rw [Finset.sum_div]

theorem actual_sample_abs (k : Nat) (hk : k<131072) :
    |cosineSeries 400 realCoefficient ((k:ℝ)/131072)| ≤
      |(decode (FapForest17.output.getD k (0,0))).re| + 1/50000000000000000 := by
  have herr := FapForest17.sample_error (input_mass_le 131072 (by norm_num)) k hk
  have hr := (Complex.abs_re_le_norm
    (decode (FapForest17.output.getD k (0,0))-
      dftSum 131072 k (negativeRoot 131072) (fun j => decode (input 131072 j)))).trans herr
  rw [Complex.sub_re, actual_dft_re 131072 k (by norm_num)] at hr
  calc
    _ = |(decode (FapForest17.output.getD k (0,0))).re -
        ((decode (FapForest17.output.getD k (0,0))).re-cosineSeries 400 realCoefficient ((k:ℝ)/131072))| := by
      congr 1; ring
    _ ≤ |(decode (FapForest17.output.getD k (0,0))).re| +
        |(decode (FapForest17.output.getD k (0,0))).re-cosineSeries 400 realCoefficient ((k:ℝ)/131072)| := abs_sub _ _
    _ ≤ _ := add_le_add le_rfl hr

/-- The finite full-transform certificate bounds every actual cosine sample. -/
theorem actual_average_bound :
    (∑k ∈ Finset.range 131072, |cosineSeries 400 realCoefficient ((k:ℝ)/131072)|)/131072 ≤
      (FapForest17.totalAbs:ℝ)/((unit:ℝ)*131072) + 1/50000000000000000 := by
  have hs := Finset.sum_le_sum (fun k hk => actual_sample_abs k (Finset.mem_range.mp hk))
  have hd := div_le_div_of_nonneg_right hs (by norm_num : (0:ℝ)≤131072)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hd
  have hlen : FapForest17.output.length = 131072 := by
    simpa using FapForest17.complete_execution.output_length
  rw [sum_decoded_real_abs FapForest17.output 131072 hlen] at hd
  change _ ≤ ((FapForest17.totalAbs:ℝ)/(unit:ℝ) + (131072:ℝ)*(1/50000000000000000))/131072 at hd
  convert hd using 1 <;> ring

lemma quad_eq_checked_accumulator : quadNumerator = FapForest17.quad := by
  exact (range_foldl_sum 400 (fun j => 20*j*j*(coefficient j).natAbs)).symm

/-- Closed periodic norm, including exact integer absolute sum, true FFT
roundoff, and actual coefficient curvature. This theorem is KERNEL-ONLY;
it is not source-first PV of the C program. -/
theorem kernel_periodic_norm :
    (∫ y in (0:ℝ)..1, |nodalPolynomial FapPV.Data.affineNodes y|) ≤
      (FapForest17.sourceNumerator:ℝ)/1000000000000000000 := by
  have hquad := periodic_integral_bound 131072 (by norm_num)
  have havg := actual_average_bound
  apply hquad.trans
  have hstep := add_le_add havg (le_refl ((quadNumerator:ℝ)/(3*10000000000000000*(131072:ℝ)^2)))
  apply hstep.trans
  rw [quad_eq_checked_accumulator, FapForest17.total_checked, FapForest17.quad_checked,
    FapForest17.numerator_checked]
  norm_num [unit]

/-- The original locked 0.7817960157900848 cap is now a proved kernel-only
numerical fact, conditional only on the explicitly named general BR norm
identity. No C execution correspondence is asserted by this theorem. -/
theorem kernel_actual_norm (hBRNorm : SourceBRFourierNormFive) :
    (∫ u : ℝ, |inverseCosine (affineSpectrum FapPV.Data.affineNodes 80) u|) ≤
      (7817960157900848:ℝ)/10000000000000000 := by
  rw [hBRNorm FapPV.Data.affineNodes 80 (by norm_num)
    (by simpa using FapPV.Data.affineNodes_length) actual_terminal]
  apply kernel_periodic_norm.trans
  rw [FapForest17.numerator_checked]
  norm_num

#print axioms actual_average_bound
#print axioms kernel_periodic_norm
#print axioms kernel_actual_norm
end RH080Next.Primal.FapFFTKernel
