/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSCanonicalZero
import IEANTN.Nodes.CMSZeroSummation.v1.Conclusions
set_option autoImplicit false

/-- Exact generated Challenge interface, proved without any imported assumption. -/
theorem CMSZeroSummation.v1.challenge_partial_summation : CMSZeroSummation.v1.partial_summation :=
  RH080Next.Explicit.canonical_zero_partial_summation_kernel

#print axioms CMSZeroSummation.v1.challenge_partial_summation
