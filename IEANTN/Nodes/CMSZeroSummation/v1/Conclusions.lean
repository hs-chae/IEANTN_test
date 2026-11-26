/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.CMSExplicitInputs.v1.Conclusions

namespace CMSZeroSummation.v1

/-- General weighted zero partial summation, with exactly the existing canonical
contract. This rule derives actual positive/negative zero-series convergence and
bounds from the literal CMS zero-counting input and the stated analytic
admissibility hypotheses. The rule itself has an unconditional kernel proof;
it does not assert the zero-counting estimate without its source input.
Primary comparison: Carneiro--Milinovich--Soundararajan, arXiv:1708.04122v2,
Section 6.1, printed pp. 23--24, Lemma 9 and the following unnumbered display.
The display is specialized in the paper; its general form here is independently
proved by finite-cutoff FTC/Fubini, smoothing, limits and conjugation. -/
def partial_summation : Prop := CMSExplicitInputs.v1.zero_partial_summation

end CMSZeroSummation.v1
