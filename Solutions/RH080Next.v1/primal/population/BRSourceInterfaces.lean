/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.BRFourierInput.v1.Conclusions
import IEANTN.Nodes.AffineFourierPrograms.v1.Conclusions
import IEANTN.Nodes.RHWeightedPopulation.v1.Conclusions
import ExplicitBRPopulationConsumer

set_option autoImplicit false
noncomputable section
namespace RH080Next.PopulationCanonical

/-- The canonical literature node has exactly the analytic contract consumed
by the affine witness proofs, with identical syntax and ordinary-RH premises. -/
theorem norm_source_exact :
    BRFourierInput.v1.norm_identity = Explicit.SourceBRFourierNormFive := rfl

theorem population_source_exact :
    BRFourierInput.v1.uniform_population_q1 = Explicit.SourceBRUniformPopulationQ1 := rfl

theorem window_construction_exact (nodes : List ℚ) (m : ℕ) :
    IEANTN.AffineFourierWindow.affineSpectrum nodes m = Explicit.affineSpectrum nodes m := rfl

theorem inverse_construction_exact (W : ℝ → ℝ) :
    IEANTN.AffineFourierWindow.inverseCosine W = Explicit.inverseCosine W := rfl

theorem polynomial_construction_exact (nodes : List ℚ) :
    IEANTN.AffineFourierWindow.nodalPolynomial nodes = Explicit.nodalPolynomial nodes := rfl

#print axioms norm_source_exact
#print axioms population_source_exact
end RH080Next.PopulationCanonical
