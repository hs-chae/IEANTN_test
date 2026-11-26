/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSZeroKernelAudit
import ExplicitCMSCanonicalZero
import Lean
set_option autoImplicit false
open Lean Elab Command
example : CMSExplicitInputs.v1.zero_partial_summation :=
  RH080Next.Explicit.canonical_zero_partial_summation_kernel
run_cmd do
  let env←getEnv
  let root:=`RH080Next.Explicit.canonical_zero_partial_summation_kernel
  let some (.thmInfo info):=env.find? root | throwError "Missing exact canonical zero proposition proof"
  let axioms←collectAxioms root
  unless axioms.all (#[`propext,`Classical.choice,`Quot.sound].contains) do throwError "Forbidden canonical zero axiom"
  unless info.value.getUsedConstants.contains `RH080Next.Explicit.cms_zero_partial_summation_kernel do
    throwError "Canonical proposition does not consume the proved kernel result"
  logInfo m!"CMS_ZERO_CANONICAL_AXIOMS {axioms}"
  logInfo "CMS_ZERO_CANONICAL_AUDIT_PASS exact-CMSExplicitInputs-v1-proposition unchanged-historical-node additive-kernel-proof no-source-scheme-premise Std3"
