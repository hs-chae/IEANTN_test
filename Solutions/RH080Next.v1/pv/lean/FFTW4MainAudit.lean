import FFTW4MainConsumers
import PopulationEnvelopeConsumers
import Lean

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
noncomputable section
open Lean Elab Command

section ActualFinalTypes
open Real RH080Next.Explicit RH080Next.FiniteGap RH080Next.FFTPV.W4Main
variable (hNorm : SourceBRFourierNormFive) (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hDigamma : SourceDLMFDigammaIntegral)
    (hCount : SourceCMSZeroCounting) (hEta : SourceDLMFRealEtaIntegral)
    (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
example (hgap : HistoricalFiniteGap) : ∀ x : ℝ, 4≤x →
    ∃ p : ℕ, Nat.Prime p ∧ x<(p:ℝ) ∧
      (p:ℝ)<x+(425531/500000:ℝ)*sqrt x*log x :=
  source_w4_global hNorm hBR hCMS hDigamma hCount hEta hMV hRH hgap
example : ∀ α : ℝ, 0≤α →
    sInf (IEANTN.CMSFunctional.goodCoefficients α)<
      (851061745/1000000000:ℝ)+(1505657839/1000000000:ℝ)*α := by
  intro α hα
  simpa only [RH080Next.ExplicitProfiles.w4RecordedPopulationWidth] using
    source_w4_population_inf_lt hNorm hBR hCMS hDigamma hCount hEta hMV hRH α hα
example (hgap : HistoricalFiniteGap) : ∀ x : ℝ, 4≤x →
    ∃ p : ℕ, Nat.Prime p ∧ x<(p:ℝ) ∧
      (p:ℝ)<x+bestWidth x*sqrt x*log x :=
  source_piecewise hNorm hBR hCMS hDigamma hCount hEta hMV hRH hgap
end ActualFinalTypes

/-- The finite N24 leaf APIs have a separate complete source-cold typed and
axiom audit. Stop expansion at their individual data/checker modules here;
full collectAxioms below still checks every final proof closure. -/
private partial def sourceClosure (env : Environment) : List Name → NameSet → NameSet
  | [],seen=>seen
  | name::rest,seen=>
    if seen.contains name then sourceClosure env rest seen else
    let seen:=seen.insert name
    if name.toString.startsWith "W4DAG24.W4D24" || name.toString.startsWith "_private.W4D24" then sourceClosure env rest seen else
    if !(name.toString.startsWith "RH080Next." || name.toString.startsWith "W4DAG24." ||
        name.toString.startsWith "FapForest17." || name.toString.startsWith "GoldbachDirect." ||
        name.toString.startsWith "_private.") then sourceClosure env rest seen else
    match env.find? name with
    | none=>sourceClosure env rest seen
    | some info=>
      let used:=info.type.getUsedConstants
      let used:=match info with
        | .thmInfo t=>used++t.value.getUsedConstants
        | .defnInfo t=>used++t.value.getUsedConstants
        | .opaqueInfo t=>used++t.value.getUsedConstants
        | _=>used
      sourceClosure env (used.toList++rest) seen

run_cmd do
  let env←getEnv
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let sourceRoots:=#[`RH080Next.FFTPV.W4Main.source_w4_global,
    `RH080Next.FFTPV.W4Main.source_w4_population,
    `RH080Next.FFTPV.W4Main.source_w4_population_inf_lt,
    `RH080Next.FFTPV.W4Main.source_piecewise,
    `RH080Next.PopulationEnvelope.source_three_curve,
    `RH080Next.PopulationEnvelope.actual_coefficient_below_both_printed_lines]
  -- One genuine conjunction contains every selected proof as a direct
  -- component. Its axiom union covers each root, with shared numerical
  -- dependencies visited once instead of repeating the enormous trace scan.
  let control:=`RH080Next.FFTPV.W4Main.matched_kernel_fft_global
  let allRoots:=sourceRoots.push control
  let last:=allRoots.back!
  let some lastInfo:=env.find? last | throwError "Missing final bundle component"
  unless lastInfo.levelParams.isEmpty do throwError "Unexpected universe parameters"
  let mut bundleType:=lastInfo.type
  let mut bundleValue:=mkConst last
  for root in allRoots.toList.reverse.tail do
    let some info:=env.find? root | throwError "Missing bundle proof {root}"
    unless info.levelParams.isEmpty do throwError "Unexpected proof universe parameters"
    bundleValue:=mkApp4 (mkConst ``And.intro) info.type bundleType (mkConst root) bundleValue
    bundleType:=mkApp2 (mkConst ``And) info.type bundleType
  let bundleName:=`RH080Next.FFTPV.W4MainAudit.selected_proof_bundle
  liftCoreM <| addDecl (.thmDecl {name:=bundleName,levelParams:=[],type:=bundleType,value:=bundleValue})
  let checkedEnv←getEnv
  let some (.thmInfo bundleInfo):=checkedEnv.find? bundleName | throwError "Kernel bundle absent"
  for root in allRoots do
    unless bundleInfo.value.getUsedConstants.contains root do
      throwError "Proof bundle omitted component {root}"
  let axes←collectAxioms bundleName
  unless axes.all allowed.contains do throwError "Nonstandard final bundle axiom: {axes}"
  logInfo m!"W4_AGGREGATE_AXIOM_UNION roots={allRoots.size} axioms={axes} each-component-is-a-subclosure"
  for root in sourceRoots do
    let some (.thmInfo info):=env.find? root | throwError "Missing W4 final theorem {root}"
    unless !(info.type.getUsedConstants.contains `RH080Next.Explicit.SourceCMSZeroPartialSummationProofScheme) do
      throwError "Final W4 theorem retains the old unproved scheme premise"
    let used:=sourceClosure env [root] {}
    for required in #[`RH080Next.FFTPV.W4Main.source_first_actual_norm,
      `RH080Next.FFTPV.W4Main.actual_main_result,
      `RH080Next.FFTPV.W4Main.main_output_actual_norm,
      `RH080Next.FFTPV.MainIO.result_value_eq,
      `RH080Next.FFTPV.MainIO.actual_result,
      `RH080Next.FFTPV.MainIO.every_main_call,
      `RH080Next.FFTPV.MainIO.actual_main_success,
      `RH080Next.FFTPV.MainIO.source_main_call,
      `RH080Next.FFTPV.MainIO.every_printf_arguments,
      `RH080Next.FFTPV.MainIO.main_body,
      `RH080Next.FFTPV.MainSuffix.norm_call_exists,
      `RH080Next.FFTPV.MainSuffix.every_norm_call,
      `RH080Next.FFTPV.MainCertificate.w4Certificate,
      `RH080Next.FFTPV.MainCertificate.w4_certificate_sum,
      `W4DAG24.complete_execution,`W4DAG24.total_checked,`W4DAG24.quad_checked,
      `RH080Next.Explicit.cms_zero_partial_summation_kernel] do
      unless used.contains required do throwError "Missing actual W4 source/math dependency {root}: {required}"
    logInfo m!"W4_FULL_MAIN_ANT_ROOT {root} aggregate_axiom_superset={axes} sourceClosure={used.toList.length}"
  let used:=sourceClosure env [control] {}
  unless used.contains `W4DAG24.kernel_actual_norm do throwError "Matched control omitted the exact kernel numerical fact"
  for forbidden in #[`RH080Next.FFTPV.MainIO.result_value_eq,
    `RH080Next.FFTPV.MainIO.actual_result,`RH080Next.FFTPV.W4Main.source_first_actual_norm] do
    if used.contains forbidden then throwError "FFT-source layer unexpectedly remains in matched control: {forbidden}"
  logInfo m!"W4_MATCHED_KERNEL_CONTROL aggregate_axiom_superset={axes} sourceClosure={used.toList.length} common-scalar-provider-inputs-preserved"
  logInfo "W4_FULL_MAIN_ANT_AUDIT_PASS source-roots=6 matched-control=1 exact-types Std3 no-native numerical-norm-premises=0 zero-scheme-premises=0 fullMainIO-and-N24-consumed"
