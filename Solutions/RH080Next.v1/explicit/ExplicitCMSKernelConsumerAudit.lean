import ExplicitCMSKernelConsumers
import ExplicitCMSKernelFapConsumers
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command
private def conjugationProofValue? : ConstantInfo → Option Expr
  | .thmInfo info=>some info.value
  | .defnInfo info=>some info.value
  | _=>none
private partial def conjugationProofClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | []=>seen
  | n::rest=>if seen.contains n then conjugationProofClosure env rest seen else
    let seen:=seen.insert n
    match env.find? n with
    | some info=>match conjugationProofValue? info with
      | some body=>conjugationProofClosure env (body.getUsedConstants.toList++rest) seen
      | none=>conjugationProofClosure env rest seen
    | none=>conjugationProofClosure env rest seen
run_cmd do
  let env←getEnv
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let roots:=#[
    `RH080Next.ExplicitProfiles.fap_08_full_kernel_of_norm,
    `RH080Next.ExplicitProfiles.fap_074_full_kernel_of_norm,
    `RH080Next.ExplicitProfiles.fap_075_full_kernel_of_norm,
    `RH080Next.ExplicitProfiles.w4_global_full_kernel_of_norm,
    `RH080Next.ExplicitProfiles.w4_recorded_population_kernel_of_norm,
    `RH080Next.ExplicitProfiles.w4_recorded_population_inf_lt_kernel_of_norm,
    `RH080Next.Primal.FapFFTKernel.kernel_fap_08_full_without_zero_scheme,
    `RH080Next.Primal.FapFFTKernel.kernel_fap_074_full_without_zero_scheme,
    `RH080Next.Primal.FapFFTKernel.kernel_fap_075_full_without_zero_scheme]
  for root in roots do
    let some (.thmInfo info) := env.find? root | throwError "Missing final CMS consumer theorem {root}"
    let axioms←collectAxioms root
    unless axioms.all allowed.contains do throwError "Nonstandard final CMS consumer axiom {root}: {axioms}"
    logInfo m!"CMS_KERNEL_CONSUMER_AXIOMS {root}: {axioms}"
    unless !info.type.getUsedConstants.contains `RH080Next.Explicit.SourceCMSZeroPartialSummationProofScheme do
      throwError "Unformalized generic scheme remains an assumption in final consumer {root}"
    let used:=conjugationProofClosure env [root]
    unless used.contains `RH080Next.Explicit.cms_zero_partial_summation_kernel do
      throwError "Proved generic zero theorem is not consumed by {root}"
  let finalFap:=#[`RH080Next.Primal.FapFFTKernel.kernel_fap_08_full_without_zero_scheme,
    `RH080Next.Primal.FapFFTKernel.kernel_fap_074_full_without_zero_scheme,
    `RH080Next.Primal.FapFFTKernel.kernel_fap_075_full_without_zero_scheme]
  for root in finalFap do
    let some (.thmInfo info) := env.find? root | throwError "Missing final originalFap theorem"
    for forbidden in #[`RH080Next.ExplicitProfiles.fapOriginalNormCap,`RH080Next.Explicit.inverseCosine] do
      unless !info.type.getUsedConstants.contains forbidden do throwError "Numerical norm remains a premise {root}"
    let used:=conjugationProofClosure env [root]
    unless used.contains `RH080Next.Primal.FapFFTKernel.kernel_actual_norm do
      throwError "Actual originalN17 numerical norm is not consumed {root}"
  logInfo m!"CMS_KERNEL_CONSUMER_AUDIT_PASS roots={roots.size} original-claims-preserved six-no-scheme-consumers three-originalFap-no-numerical-norm-premises all-consume-kernel-zero-theorem actualN17-FFT-kernel-only other-literal-inputs-explicit Std3"
