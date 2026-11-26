/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSZeroKernel
import IEANTN.Nodes.CMSExplicitInputs.v1.Conclusions
set_option autoImplicit false
namespace RH080Next.Explicit

/-- Additive exact correspondence to the existing canonical proposition;
no historical node, source predicate or old outcome is changed. -/
theorem canonical_zero_partial_summation_kernel : CMSExplicitInputs.v1.zero_partial_summation:=by
  change SourceCMSZeroPartialSummationProofScheme
  exact cms_zero_partial_summation_kernel

#print axioms canonical_zero_partial_summation_kernel
end RH080Next.Explicit
