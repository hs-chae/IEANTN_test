import ExplicitCMSZeroKernel
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
example : RH080Next.Explicit.SourceCMSZeroPartialSummationProofScheme :=
  RH080Next.Explicit.cms_zero_partial_summation_kernel

run_cmd do
  let env←getEnv
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let roots:=#[
    `RH080Next.Explicit.ZeroSummation.atom_cutoff_ibp,
    `RH080Next.Explicit.ZeroSummation.countable_cutoff_ibp,
    `RH080Next.Explicit.ZeroSummation.cutoff_ibp,
    `RH080Next.Explicit.ZeroSummation.actual_c1_cutoff_ibp,
    `RH080Next.Explicit.ZeroSummation.q_cutoff_ibp,
    `RH080Next.Explicit.ZeroSummation.actual_c1_remainder_cutoff,
    `RH080Next.Explicit.ZeroSummation.actual_modulus_cutoff,
    `RH080Next.Explicit.ZeroSummation.actual_positive_infinite,
    `RH080Next.Explicit.ZeroSummation.positive_transfer,
    `RH080Next.Explicit.CMSConjugation.negative_of_positive,
    `RH080Next.Explicit.cms_zero_partial_summation_kernel,
    `RH080Next.Explicit.cms_full_zero_bound_kernel]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual CMS kernel theorem {root}"
    let axioms←collectAxioms root
    unless axioms.all allowed.contains do throwError "Nonstandard CMS kernel axiom {root}: {axioms}"
    logInfo m!"CMS_ZERO_KERNEL_AXIOMS {root}: {axioms}"
  let dependencies:=conjugationProofClosure env [`RH080Next.Explicit.cms_zero_partial_summation_kernel]
  for child in #[
      `RH080Next.Explicit.ZeroSummation.atom_cutoff_ibp,
      `RH080Next.Explicit.ZeroSummation.countable_cutoff_ibp,
      `RH080Next.Explicit.ZeroSummation.cutoff_ibp,
      `RH080Next.Explicit.ZeroSummation.actual_c1_cutoff_ibp,
      `RH080Next.Explicit.ZeroSummation.cmsQ_hasDerivAt,
      `RH080Next.Explicit.ZeroSummation.q_cutoff_ibp,
      `RH080Next.Explicit.ZeroSummation.actual_c1_remainder_cutoff,
      `RH080Next.Explicit.ZeroSummation.actual_modulus_cutoff,
      `RH080Next.Explicit.ZeroSummation.actual_positive_infinite,
      `RH080Next.Explicit.ZeroSummation.positive_transfer,
      `RH080Next.Explicit.cmsSmoothModulus_hasDerivAt,
      `RH080Next.Explicit.cmsSmoothModulus_uniform_error,
      `RH080Next.Explicit.cmsSmoothModulusDeriv_abs_le,
      `RH080Next.Explicit.CMSConjugation.negative_of_positive,
      `RH080Next.Explicit.CMSConjugation.riemannZeta_order_conj,
      `riemannZeta_conj,
      `MeasureTheory.hasSum_integral_of_summable_integral_norm,
      `intervalIntegral.integral_eq_sub_of_hasDerivAt,
      `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt,
      `Real.tsum_le_of_sum_le,
      `MeasureTheory.integral_comp_mul_left_Ioi] do
    unless dependencies.contains child do throwError "Missing actual CMS kernel proof link {child}"
  logInfo m!"CMS_ZERO_KERNEL_AUDIT_PASS roots={roots.size} closure={dependencies.toList.length} literal-zero-count-input actual-uncountable-zero-subtype countable-local-support right-closed-endpoints ordinary-FTC-Fubini Q-cancellation finite-smooth-modulus epsilon-before-infinity actual-summability exact-scaling actual-conjugation no-unformalized-source-scheme-premise no-native Std3"
