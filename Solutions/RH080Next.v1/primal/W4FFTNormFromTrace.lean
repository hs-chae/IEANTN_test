/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import W4FFTNodes
import W4FFTGlobalTraceBounds
import FFTUpwardNormalization
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
noncomputable section
open scoped BigOperators Interval
open Real MeasureTheory
namespace RH080Next.Primal.W4FFTKernel
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

theorem sample_abs_of_error (out : List CInt) (n : Nat) (hn : 5040≤n)
    (herr : ∀ k<n, ‖decode (out.getD k (0,0))-
      dftSum n k (negativeRoot n) (fun j => decode (W4.input n j))‖≤
      (1/100000000000000:ℝ)) (k : Nat) (hk : k<n) :
    |cosineSeries 2520 realCoefficient ((k:ℝ)/n)| ≤
      |(decode (out.getD k (0,0))).re|+1/100000000000000 := by
  have hr := (Complex.abs_re_le_norm
    (decode (out.getD k (0,0))-
      dftSum n k (negativeRoot n) (fun j => decode (W4.input n j)))).trans (herr k hk)
  rw [Complex.sub_re, actual_dft_re n k hn] at hr
  calc
    _ = |(decode (out.getD k (0,0))).re-
        ((decode (out.getD k (0,0))).re-cosineSeries 2520 realCoefficient ((k:ℝ)/n))| := by
      congr 1; ring
    _ ≤ |(decode (out.getD k (0,0))).re|+
        |(decode (out.getD k (0,0))).re-cosineSeries 2520 realCoefficient ((k:ℝ)/n)| := abs_sub _ _
    _ ≤ _ := add_le_add le_rfl hr

theorem average_bound (out : List CInt) (n : Nat) (hn : 5040≤n)
    (hlen : out.length=n)
    (herr : ∀ k<n, ‖decode (out.getD k (0,0))-
      dftSum n k (negativeRoot n) (fun j => decode (W4.input n j))‖≤
      (1/100000000000000:ℝ)) :
    (∑k ∈ Finset.range n, |cosineSeries 2520 realCoefficient ((k:ℝ)/n)|)/(n:ℝ) ≤
      ((out.foldl (fun a z => a+z.1.natAbs) 0:Nat):ℝ)/((unit:ℝ)*n)+1/100000000000000 := by
  have hs := Finset.sum_le_sum (fun k hk => sample_abs_of_error out n hn herr k (Finset.mem_range.mp hk))
  have hd := div_le_div_of_nonneg_right hs (by positivity : (0:ℝ)≤n)
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    sum_decoded_real_abs out n hlen] at hd
  have hn0 : 0<n := by omega
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn0.ne'
  convert hd using 1 <;> first | rfl | (field_simp [hnr, unit] <;> ring)

theorem quad_eq_source_accumulator : quadNumerator=W4.quad := by
  exact (range_foldl_sum 2520 (fun j => 20*j*j*(W4.coefficient j).natAbs)).symm

/-- A generic output-to-integral theorem. The exact FFT error premise must be
proved from an execution trace; this does not assume a stored norm answer. -/
theorem periodic_norm_from_output (out : List CInt) (n : Nat) (hn : 5040≤n)
    (hlen : out.length=n)
    (herr : ∀ k<n, ‖decode (out.getD k (0,0))-
      dftSum n k (negativeRoot n) (fun j => decode (W4.input n j))‖≤
      (1/100000000000000:ℝ)) :
    (∫ y in (0:ℝ)..1, |nodalPolynomial WindowPV.Data.affineNodes y|) ≤
      (W4.normFromOutput n out:ℝ)/10000000000000000 := by
  have hquad := periodic_integral_bound n (by omega)
  have havg := average_bound out n hn hlen herr
  apply hquad.trans
  have hstep := add_le_add havg (le_refl ((quadNumerator:ℝ)/(3*10000000000000000*(n:ℝ)^2)))
  apply hstep.trans
  rw [quad_eq_source_accumulator]
  unfold W4.normFromOutput
  have hu := w4_upward_budget (out.foldl (fun a z => a+z.1.natAbs) 0) W4.quad n (by omega)
  convert hu using 1 <;> first | rfl | ring

theorem actual_norm_from_trace24 (hBRNorm : SourceBRFourierNormFive)
    (stages : Nat → List CInt) (out : List CInt)
    (h : ExecutionTrace stages (W4.input 16777216) 24 0 1 out)
    (seed : CInt) (rest : List CInt)
    (hlen : ((unit,0)::rest).length=8388608)
    (hseed : decode seed=rootSeed)
    (htrace : TwiddleTrace seed (unit,0) rest)
    (hchain : ∀ t<24, DecimationTrace (24-(t+1)) ((unit,0)::rest) (stages (t+1))) :
    (∫ u : ℝ, |inverseCosine (affineSpectrum WindowPV.Data.affineNodes 360) u|) ≤
      (W4.normFromOutput 16777216 out:ℝ)/10000000000000000 := by
  rw [affine_norm_eq_periodic_of_five_mesh hBRNorm WindowPV.Data.affineNodes 360 504
    (by norm_num) (by norm_num) (by simpa using WindowPV.Data.affineNodes_length)
    (by simpa using actual_terminal)]
  apply periodic_norm_from_output out 16777216 (by norm_num)
  · simpa using h.output_length
  · exact h.error24 seed rest hlen hseed htrace hchain (input_mass_le 16777216 (by norm_num))

#print axioms periodic_norm_from_output
#print axioms actual_norm_from_trace24
end RH080Next.Primal.W4FFTKernel
