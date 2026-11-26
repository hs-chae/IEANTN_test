/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WindowPositiveArea
import FapPositiveArea
import WindowInputBounds
import FapInputBounds
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command
private def proofValue? : ConstantInfo → Option Expr
  | .thmInfo i => some i.value
  | .defnInfo i => some i.value
  | _ => none
private partial def proofClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n::rest => if seen.contains n then proofClosure env rest seen else
    let seen:=seen.insert n
    match env.find? n with
    | some info => match proofValue? info with
      | some body => proofClosure env (body.getUsedConstants.toList++rest) seen
      | none => proofClosure env rest seen
    | none => proofClosure env rest seen
private partial def leadingUses : Expr → List (String×Bool)
  | .lam n _ body _ => (n.toString,body.hasLooseBVar 0)::leadingUses body
  | .mdata _ body => leadingUses body
  | _ => []
run_cmd do
  let env ← getEnv
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let profiles:=#[(`RH080Next.WindowPV,`RH080Next.WindowPV.source_first_positive_leak,
      `RH080Next.WindowPV.source_first_variation),
    (`RH080Next.FapPV,`RH080Next.FapPV.source_first_positive_leak,
      `RH080Next.FapPV.source_first_variation)]
  for (ns,jroot,vroot) in profiles do
    for root in #[jroot,vroot,ns++`input_mass_bound,ns++`input_window_bound,
        ns++`actual_qPositiveArea,ns++`actual_qMassA0] do
      let some (.thmInfo _) := env.find? root | throwError "Missing theorem {root}"
      let axioms ← collectAxioms root
      unless axioms.all allowed.contains do throwError "Unverified axiom {root}: {axioms}"
      logInfo m!"ORIGINAL_ADDITIONAL_AXIOMS {root}: {axioms}"
    let jclosure:=proofClosure env [jroot]
    for child in #[ns++`actual_source_syntax,ns++`Execution.actual_positive_area_numerator,
        ns++`actual_main_output,ns++`actual_qPositiveArea,
        `RH080Next.Primal.positiveLeak_affineSpectrum_eq_nodalPositiveArea,
        `RH080Next.ScalarPositiveArea.qPositiveArea_cast] do
      unless jclosure.contains child do throwError "J source/math proof missing {jroot}->{child}"
    let vclosure:=proofClosure env [vroot]
    for child in #[ns++`actual_source_syntax,ns++`Execution.actual_first_variation_numerator,
        ns++`actual_qV0,`RH080Next.ScalarInputBounds.qV0_cast] do
      unless vclosure.contains child do throwError "V0 source/math proof missing {vroot}->{child}"
    for transport in #[ns++`source_output_positive_leak,ns++`source_output_variation] do
      let some info := env.find? transport | throwError "Missing transport {transport}"
      let some body := proofValue? info | throwError "Missing transport body {transport}"
      unless (leadingUses body).any (fun x=>x.1=="h"&&x.2) do
        throwError "Actual source output premise unused by {transport}"
  logInfo "ORIGINAL_SCALAR_ADDITIONAL_AUDIT_PASS roots=12 actual-J-and-V0-source-consumed input-A0-M-labeled no-native no-sorry"
