import ExplicitCMSConjugation
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
    `RH080Next.Explicit.CMSConjugation.conj_tendsto_nhds,
    `RH080Next.Explicit.CMSConjugation.conj_tendsto_nhdsNE,
    `RH080Next.Explicit.CMSConjugation.analyticAt_conjugate,
    `RH080Next.Explicit.CMSConjugation.order_conj,
    `RH080Next.Explicit.CMSConjugation.riemannZeta_order_conj,
    `RH080Next.Explicit.CMSConjugation.zetaOrder_conj,
    `RH080Next.Explicit.CMSConjugation.zeroConj_involutive,
    `RH080Next.Explicit.CMSConjugation.multiplicity_conj,
    `RH080Next.Explicit.CMSConjugation.signed_amplitude_conj,
    `RH080Next.Explicit.CMSConjugation.negative_of_positive]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual-zero conjugation theorem {root}"
    let axioms←collectAxioms root
    unless axioms.all allowed.contains do throwError "Nonstandard conjugation axiom {root}: {axioms}"
    logInfo m!"CMS_CONJUGATION_AXIOMS {root}: {axioms}"
  let dependencies:=conjugationProofClosure env [`RH080Next.Explicit.CMSConjugation.negative_of_positive]
  for child in #[
      `RH080Next.Explicit.CMSConjugation.order_conj,
      `RH080Next.Explicit.CMSConjugation.riemannZeta_order_conj,
      `RH080Next.Explicit.CMSConjugation.zetaOrder_conj,
      `RH080Next.Explicit.CMSConjugation.zeroConj,
      `RH080Next.Explicit.CMSConjugation.zeroConjEquiv,
      `RH080Next.Explicit.CMSConjugation.multiplicity_conj,
      `RH080Next.Explicit.CMSConjugation.signed_amplitude_conj,
      `riemannZeta_conj,`meromorphicOrderAt_eq_int_iff,
      `meromorphicOrderAt_eq_top_iff,`Equiv.summable_iff,`Equiv.tsum_eq,
      `IEANTN.zetaOrder,`RH080Next.Explicit.cmsMultiplicity,`RH080Next.Explicit.cmsSignedAmplitude] do
    unless dependencies.contains child do throwError "Missing actual zero/order/reindexing proof link {child}"
  logInfo m!"CMS_CONJUGATION_AUDIT_PASS roots={roots.size} closure={dependencies.toList.length} actual-zeta actual-meromorphic-order actual-critical-strip-zero-subtype conjugation-involution even-amplitude negative-summability real-tsum-equality no-new-literature no-RH-premise no-native no-sorry"
