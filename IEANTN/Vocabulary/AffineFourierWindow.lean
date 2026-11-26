/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Pure construction data for finite rational affine Fourier windows. The final
stored node is an implicit zero endpoint; source and witness propositions carry
its zero check explicitly. Analytic Fourier, norm and population assertions live
in nodes and Solutions. These definitions match BR v2 Lemma5, §2.1, eq:pair. -/
noncomputable section
open Real Set MeasureTheory
namespace IEANTN.AffineFourierWindow

def node (nodes : List ℚ) (j : ℕ) : ℝ := (nodes.getD j 0 : ℚ)
def hat (x : ℝ) : ℝ := max 0 (1-|x|)
def affineSpectrum (nodes : List ℚ) (m : ℕ) (v : ℝ) : ℝ :=
  node nodes 0*hat ((m : ℝ)*v)+
    ∑ j ∈ Finset.Ico 1 (nodes.length-1),
      node nodes j*(hat ((m : ℝ)*v-j)+hat ((m : ℝ)*v+j))
def inverseCosine (W : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ v : ℝ, W v*cos (2*π*u*v)
def nodalPolynomial (nodes : List ℚ) (y : ℝ) : ℝ :=
  node nodes 0+2*∑ j ∈ Finset.Ico 1 (nodes.length-1), node nodes j*cos (2*π*j*y)
end IEANTN.AffineFourierWindow
