/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import FapFFTAntConsumers
import FapRescaling
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
section ExactTheoremTypes
open Real RH080Next.Explicit RH080Next.FiniteGap RH080Next.Primal.FapFFTKernel
variable (hBRNorm : SourceBRFourierNormFive) (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hDigamma : SourceDLMFDigammaIntegral)
    (hZero : SourceCMSZeroPartialSummationProofScheme) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan)
    (hRH : RiemannHypothesis) (hgap : HistoricalFiniteGap)
example : ∀x : ℝ, 4≤x → x≤exp 174 →
    ∃p : Nat, Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)<x+(4/5:ℝ)*sqrt x*log x :=
  kernel_fap_08_full hBRNorm hBR hCMS hDigamma hZero hCount hEta hMV hRH hgap
example : ∀x : ℝ, 11≤x → x≤exp 63 →
    ∃p : Nat, Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)<x+(37/50:ℝ)*sqrt x*log x :=
  kernel_fap_074_full hBRNorm hBR hCMS hDigamma hZero hCount hEta hMV hRH hgap
example : ∀x : ℝ, 11≤x → x≤exp 70 →
    ∃p : Nat, Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)<x+(3/4:ℝ)*sqrt x*log x :=
  kernel_fap_075_full hBRNorm hBR hCMS hDigamma hZero hCount hEta hMV hRH hgap
end ExactTheoremTypes

private partial def leadingUses : Expr → List (String × Bool)
  | .lam name _ body _ => (name.toString, body.hasLooseBVar 0)::leadingUses body
  | .mdata _ body => leadingUses body
  | _ => []
private partial def mathematicalClosure (env : Environment) : List Name → List Name → List Name
  | [], seen => seen
  | name::rest, seen =>
    if seen.contains name then mathematicalClosure env rest seen else
    let seen := name::seen
    if !(name.toString.startsWith "RH080Next." || name.toString.startsWith "FapForest17." ||
      name.toString.startsWith "GoldbachDirect." || name.toString.startsWith "_private.") then
      mathematicalClosure env rest seen
    else match env.find? name with
      | none => mathematicalClosure env rest seen
      | some info =>
        let constants := info.type.getUsedConstants
        let constants := match info with
          | .thmInfo t => constants ++ t.value.getUsedConstants
          | .defnInfo t => constants ++ t.value.getUsedConstants
          | _ => constants
        mathematicalClosure env (constants.toList++rest) seen
run_cmd do
  let env ← getEnv
  let roots := #[
    `RH080Next.Primal.FapFFTKernel.decode_input_eq_symmetric,
    `RH080Next.Primal.FapFFTKernel.input_mass_le,
    `RH080Next.Primal.FapFFTKernel.actual_dft_re,
    `RH080Next.Primal.FapFFTKernel.nodalPolynomial_eq_series,
    `RH080Next.Primal.FapFFTKernel.curvature_bound,
    `RH080Next.Primal.FapFFTKernel.periodic_integral_bound,
    `RH080Next.Primal.FapFFTKernel.actual_average_bound,
    `RH080Next.Primal.FapFFTKernel.kernel_periodic_norm,
    `RH080Next.Primal.FapFFTKernel.kernel_actual_norm,
    `RH080Next.Primal.FapFFTKernel.kernel_fap_strict_slab,
    `RH080Next.Primal.FapFFTKernel.kernel_fap_08_full,
    `RH080Next.Primal.FapFFTKernel.kernel_fap_074_full,
    `RH080Next.Primal.FapFFTKernel.kernel_fap_075_full,
    `RH080Next.FapPV.affineNodes_exact_rescaling]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    let some (.thmInfo info) := env.find? root | throwError "Missing actual theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unexpected axiom {root}: {axioms}"
    logInfo m!"FAP_KERNEL_ANT_AXIOMS {root}: {axioms}"
    if root.toString.startsWith "RH080Next.Primal.FapFFTKernel.kernel_fap_" then
      let uses := leadingUses info.value
      for required in ["hBRNorm", "hBR", "hCMS", "hDigamma", "hZero", "hCount", "hEta", "hMV", "hRH"] do
        unless uses.any (fun p => p.1 == required && p.2) do throwError "Unconsumed analytic/RH input {root}: {required}"
      if root != `RH080Next.Primal.FapFFTKernel.kernel_fap_strict_slab then
        unless uses.any (fun p => p.1 == "hgap" && p.2) do throwError "Historical finite input not consumed {root}"
      if uses.any (fun p => p.1 == "hNorm" || p.1 == "hFFTNorm" || p.1 == "hSampleError") then
        throwError "Final consumer still has numerical premise {root}"
  let closure := mathematicalClosure env [`RH080Next.Primal.FapFFTKernel.kernel_fap_08_full] []
  for required in #[
    `FapForest17.complete_execution,
    `FapForest17.total_checked,
    `FapForest17.quad_checked,
    `FapForest17.numerator_checked,
    `FapForest17.sample_error,
    `RH080Next.FFT.IntegerModel.ExecutionTrace.error17,
    `RH080Next.Primal.FapFFTKernel.input_mass_le,
    `RH080Next.Primal.FapFFTKernel.actual_dft_re,
    `RH080Next.Primal.FapFFTKernel.actual_node_eq_coefficient,
    `RH080Next.Primal.FapFFTKernel.nodalPolynomial_eq_series,
    `RH080Next.Primal.cosine_series_abs_chord_quadrature,
    `RH080Next.Primal.FapFFTKernel.kernel_actual_norm,
    `RH080Next.ExplicitProfiles.fap_08_full_of_norm,
    `RH080Next.Explicit.actual_prime_interval_of_residual,
    `RH080Next.FapPV.actual_source_scalar_output] do
    unless closure.contains required do throwError "Missing actual trace/math/source-scalar dependency {required}"
  logInfo m!"FAP_KERNEL_ANT_DEPENDENCY_PASS closure={closure.length}"
  logInfo "FAP_KERNEL_ANT_AUDIT_PASS roots=14 numerical_norm_premises=0 FFT_status=KERNEL_ONLY_NOT_PV"
