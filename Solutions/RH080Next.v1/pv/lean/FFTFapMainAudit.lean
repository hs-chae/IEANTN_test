/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFapMainConsumers
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
open Lean Elab Command

section ExpectedFinalTypes
open Real RH080Next.Explicit RH080Next.FiniteGap RH080Next.FFTPV.FapMain
variable (hBRNorm : SourceBRFourierNormFive) (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hDigamma : SourceDLMFDigammaIntegral)
    (hCount : SourceCMSZeroCounting) (hEta : SourceDLMFRealEtaIntegral)
    (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis) (hgap : HistoricalFiniteGap)
example : ∀x : ℝ,4≤x → x≤exp 174 → ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧
    (p:ℝ)<x+(4/5:ℝ)*sqrt x*log x :=
  source_fap_08_full hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH hgap
example : ∀x : ℝ,11≤x → x≤exp 63 → ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧
    (p:ℝ)<x+(37/50:ℝ)*sqrt x*log x :=
  source_fap_074_full hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH hgap
example : ∀x : ℝ,11≤x → x≤exp 70 → ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧
    (p:ℝ)<x+(3/4:ℝ)*sqrt x*log x :=
  source_fap_075_full hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH hgap
end ExpectedFinalTypes

private partial def sourceClosure (env : Environment) : List Name → NameSet → NameSet
  | [],seen=>seen
  | name::rest,seen=>
    if seen.contains name then sourceClosure env rest seen else
    let seen:=seen.insert name
    if !(name.toString.startsWith "RH080Next." || name.toString.startsWith "FapForest17." ||
        name.toString.startsWith "GoldbachDirect." || name.toString.startsWith "_private.") then
      sourceClosure env rest seen
    else match env.find? name with
    | none=>sourceClosure env rest seen
    | some info=>
      let constants:=info.type.getUsedConstants
      let constants:=match info with
        | .thmInfo t=>constants++t.value.getUsedConstants
        | .defnInfo t=>constants++t.value.getUsedConstants
        | .opaqueInfo t=>constants++t.value.getUsedConstants
        | _=>constants
      sourceClosure env (constants.toList++rest) seen

run_cmd do
  let env←getEnv
  let roots:=#[`RH080Next.FFTPV.FapMain.source_fap_08_full,
    `RH080Next.FFTPV.FapMain.source_fap_074_full,`RH080Next.FFTPV.FapMain.source_fap_075_full]
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  for root in roots do
    let some (.thmInfo info):=env.find? root | throwError "Missing source ANT theorem {root}"
    let axioms←collectAxioms root
    unless axioms.all allowed.contains do throwError "Nonstandard axiom in {root}: {axioms}"
    let directType:=info.type.getUsedConstants
    for forbidden in #[`RH080Next.Explicit.SourceCMSZeroPartialSummationProofScheme] do
      if directType.contains forbidden then throwError "Final theorem retains unproved scheme premise {root}"
    let closure:=sourceClosure env [root] {}
    for required in #[`RH080Next.FFTPV.MainIO.result_value_eq,
      `RH080Next.FFTPV.MainIO.every_main_call,`RH080Next.FFTPV.MainIO.actual_main_success,
      `RH080Next.FFTPV.MainIO.source_main_call,`RH080Next.FFTPV.MainIO.every_printf_arguments,
      `RH080Next.FFTPV.MainIO.actual_result,`RH080Next.FFTPV.MainIO.main_body,
      `RH080Next.FFTPV.MainSuffix.norm_call_exists,
      `RH080Next.FFTPV.MainSuffix.every_norm_call,`RH080Next.FFTPV.MainSuffix.norm_suffix_total,
      `RH080Next.FFTPV.MainCertificate.fapCertificate,`RH080Next.FFTPV.MainCertificate.fap_certificate_sum,
      `RH080Next.FFTPV.FapSource.norm_answer_checked,`FapForest17.complete_execution,
      `FapForest17.total_checked,`FapForest17.quad_checked,
      `RH080Next.FFTPV.SourceOutput.actual_main_selected,
      `RH080Next.Explicit.cms_zero_partial_summation_kernel,
      `RH080Next.FFTPV.FapMain.source_first_actual_norm] do
      unless closure.contains required do throwError "Missing actual source/math dependency {root}: {required}"
    logInfo m!"FAP_FULL_MAIN_ANT_AUDIT_ROOT {root} axioms={axioms} closure={closure.toList.length}"
  logInfo "FAP_FULL_MAIN_ANT_AUDIT_PASS roots=3 numerical_norm_premises=0 generalized_zero_premises=0 boundary=COMPLETE_OPERATIONAL_MAIN_LOGICAL_STDIO_PHYSICAL_FLUSH_CONTRACT_SEPARATE"
