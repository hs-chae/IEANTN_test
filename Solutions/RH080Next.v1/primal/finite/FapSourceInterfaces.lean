/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.CMSExplicitInputs.v1.Conclusions
import IEANTN.Nodes.BRFourierInput.v1.Conclusions
import IEANTN.Nodes.FapFourierNorm.v1.Tables
import ExplicitGuinandWeilApplication
import ExplicitCMSZeroSource
import ExplicitMontgomeryVaughan
import ExplicitNormSourceBridge
import FinitePrimeGapBridge
import FapAffineData

namespace RH080Next.Primal.FiniteCanonical

/-- Literal source statements, including all domains/convergence and the
explicit generalized proof-scheme distinction, are preserved definitionally. -/
theorem strip_interface : CMSExplicitInputs.v1.strip_regularity = RH080Next.Explicit.SourceBRFourierNormStrip := rfl
theorem guinand_interface : CMSExplicitInputs.v1.guinand_weil = RH080Next.Explicit.SourceCMSGuinandWeil := rfl
theorem digamma_interface : CMSExplicitInputs.v1.digamma_integral = RH080Next.Explicit.SourceDLMFDigammaIntegral := rfl
theorem eta_interface : CMSExplicitInputs.v1.real_eta_integral = RH080Next.Explicit.SourceDLMFRealEtaIntegral := rfl
theorem count_interface : CMSExplicitInputs.v1.zero_counting = RH080Next.Explicit.SourceCMSZeroCounting := rfl
theorem partial_interface : CMSExplicitInputs.v1.zero_partial_summation = RH080Next.Explicit.SourceCMSZeroPartialSummationProofScheme := rfl
theorem mv_interface : CMSExplicitInputs.v1.montgomery_vaughan = RH080Next.Explicit.SourceMontgomeryVaughan := rfl
theorem historical_interface : CMSExplicitInputs.v1.historical_finite_gap = RH080Next.FiniteGap.HistoricalFiniteGap := rfl
theorem norm_interface : BRFourierInput.v1.norm_identity = RH080Next.Explicit.SourceBRFourierNormFive := rfl

/-- Exact original data, with identical finite-array operations and scale. -/
theorem table_nodes_exact : FapFourierNorm.v1.Tables.affineNodes = RH080Next.FapPV.Data.affineNodes := rfl

#print axioms table_nodes_exact
end RH080Next.Primal.FiniteCanonical
