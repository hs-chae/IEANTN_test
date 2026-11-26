import FFTFapMainConsumers
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory
namespace IndependentFinalMathReview
open RH080Next.Explicit RH080Next.ExplicitProfiles RH080Next.FiniteGap

example (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hD : SourceDLMFDigammaIntegral) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan)
    (hRH : RiemannHypothesis) (hgap : HistoricalFiniteGap)
    (hn : (∫ u : ℝ, |inverseCosine (affineSpectrum w4Nodes 360) u|) ≤ w4OriginalNormCap)
    (x : ℝ) (hx : 4 ≤ x) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p:ℝ) ∧
      (p:ℝ) < x + (425531/500000:ℝ)*sqrt x*log x :=
  w4_global_full_kernel_of_norm hBR hCMS hD hCount hEta hMV hRH hgap hn x hx

example (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hD : SourceDLMFDigammaIntegral) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan)
    (hRH : RiemannHypothesis)
    (hn : (∫ u : ℝ, |inverseCosine (affineSpectrum w4Nodes 360) u|) ≤ w4OriginalNormCap)
    (α : ℝ) (hα : 0 ≤ α) :
    sInf (IEANTN.CMSFunctional.goodCoefficients α) <
      (851061745/1000000000:ℝ)+(1505657839/1000000000:ℝ)*α :=
  w4_recorded_population_inf_lt_kernel_of_norm hBR hCMS hD hCount hEta hMV hRH hn α hα

example (hNorm : SourceBRFourierNormFive) (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hD : SourceDLMFDigammaIntegral)
    (hCount : SourceCMSZeroCounting) (hEta : SourceDLMFRealEtaIntegral)
    (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis) (hgap : HistoricalFiniteGap)
    (x : ℝ) (hx : 4 ≤ x) (hX : x ≤ exp 174) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p:ℝ) ∧ (p:ℝ)<x+(4/5:ℝ)*sqrt x*log x :=
  RH080Next.FFTPV.FapMain.source_fap_08_full hNorm hBR hCMS hD hCount hEta hMV hRH hgap x hx hX

open Lean Elab Command
private def proofValue? : ConstantInfo → Option Expr
  | .thmInfo info => some info.value
  | .defnInfo info => some info.value
  | _ => none
private partial def proofClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n::rest => if seen.contains n then proofClosure env rest seen else
      let seen := seen.insert n
      match env.find? n with
      | some info => match proofValue? info with
        | some body => proofClosure env (body.getUsedConstants.toList ++ rest) seen
        | none => proofClosure env rest seen
      | none => proofClosure env rest seen
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let finiteRoots := #[
    `RH080Next.ExplicitProfiles.fap_08_full_kernel_of_norm,
    `RH080Next.ExplicitProfiles.fap_074_full_kernel_of_norm,
    `RH080Next.ExplicitProfiles.fap_075_full_kernel_of_norm,
    `RH080Next.ExplicitProfiles.w4_global_full_kernel_of_norm]
  let weightedRoots := #[
    `RH080Next.ExplicitProfiles.w4_recorded_population_kernel_of_norm,
    `RH080Next.ExplicitProfiles.w4_recorded_population_inf_lt_kernel_of_norm]
  let mainRoots := #[
    `RH080Next.FFTPV.FapMain.source_fap_08_full,
    `RH080Next.FFTPV.FapMain.source_fap_074_full,
    `RH080Next.FFTPV.FapMain.source_fap_075_full]
  let zero := `RH080Next.Explicit.cms_zero_partial_summation_kernel
  for root in finiteRoots ++ weightedRoots ++ mainRoots do
    let some (.thmInfo info) := env.find? root | throwError "Missing actual theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Nonstandard axiom {root}: {axioms}"
    unless !info.type.getUsedConstants.contains `RH080Next.Explicit.SourceCMSZeroPartialSummationProofScheme do
      throwError "Generic zero proof scheme persists in theorem type {root}"
    let used := proofClosure env [root]
    unless used.contains zero do throwError "Actual proved zero transfer absent {root}"
    unless used.contains `RH080Next.Explicit.affine_strip_extension_by_mesh_dilation do
      throwError "Actual support5-to7 strip extension absent {root}"
    logInfo m!"INDEPENDENT_TYPE {root}: {info.type}"
    logInfo m!"INDEPENDENT_AXIOMS {root}: {axioms}"
  for root in finiteRoots ++ mainRoots do
    let used := proofClosure env [root]
    for required in #[`RH080Next.Explicit.signed_log_affine_inverse_three_eighths,
        `RH080Next.Explicit.explicit_budget_assembly,
        `RH080Next.Explicit.strict_prime_of_two_halfopen] do
      unless used.contains required do throwError "Actual analytic/strict endpoint dependency absent {root}: {required}"
  for root in mainRoots do
    let some (.thmInfo info) := env.find? root | throwError "Missing source-first final theorem"
    for forbidden in #[`RH080Next.ExplicitProfiles.fapOriginalNormCap,
        `RH080Next.Explicit.inverseCosine] do
      unless !info.type.getUsedConstants.contains forbidden do
        throwError "Undischarged norm hypothesis in {root}"
    let used := proofClosure env [root]
    unless used.contains `RH080Next.FFTPV.FapMain.actual_main_result do
      throwError "Actual full C-main result not consumed {root}"
  logInfo "INDEPENDENT_FINAL_MATH_PASS nine actual conclusions; strict endpoints, kernel zero transfer, signed moment, unchanged budget, support dilation, and three full-main numerical consumers checked"
end IndependentFinalMathReview
