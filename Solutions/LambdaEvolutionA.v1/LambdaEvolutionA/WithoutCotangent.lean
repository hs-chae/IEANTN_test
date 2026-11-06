/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LambdaEvolutionA.PsiCompanion
import CotangentSeriesProof

namespace LambdaEvolutionA

/-- The twelve remaining CH2 inputs. The cotangent-series statement is proved
by the isolated solution and is not an argument of this package. -/
structure DirectCH2Inputs12 : Prop where
  hfe : ZetaLogDeriv.v1.logDeriv_functional_equation
  hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip
  h24u : CH2.v2.proposition_2_4_upper
  h24l : CH2.v2.proposition_2_4_lower
  hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating
  hneg : ZetaLogDerivValues.v1.logDeriv_neg_one
  h2v : ZetaLogDerivValues.v1.logDeriv_two
  hv : ZetaLogDerivValues.v1.logDeriv_three_halves
  hrvm : ZeroCount.v1.rvm_error_bound
  hsmall : ZeroCount.v1.rvm_error_small
  hlow : LowZeroes.v1.no_zeroes_below_first_ordinate
  hH : ZetaHadamard.v1.logDeriv_partial_fractions

theorem DirectCH2Inputs12.toDirect (h : DirectCH2Inputs12) : DirectCH2Inputs where
  hfe := h.hfe
  hdig := h.hdig
  h24u := h.h24u
  h24l := h.h24l
  hk := h.hk
  hneg := h.hneg
  h2v := h.h2v
  hv := h.hv
  hcs := CotangentSeriesSolution.cot_series_zeta_values
  hrvm := h.hrvm
  hsmall := h.hsmall
  hlow := h.hlow
  hH := h.hH

theorem direct_lambda330_without_cotangent
    (hs : DirectCH2Inputs12)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x : ℝ} (hx : Real.exp (330 : ℝ) ≤ x) :
    |CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)| ≤
      (1826923053/200000000000 : ℝ) * x ^ (-(1 : ℝ)/8) :=
  direct_lambda330 hs.toDirect h hRH hqrh hx

theorem psi_companion330_without_cotangent
    (hs : DirectCH2Inputs12)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x : ℝ} (hx : Real.exp (330 : ℝ) ≤ x) :
    IEANTN.Eψ x ≤ (1826923053/200000000000 : ℝ) * x ^ (-(1 : ℝ)/8) :=
  psi_companion330 hs.toDirect h hRH hqrh hx

theorem matched_flat_lambda330_without_cotangent
    (hs : DirectCH2Inputs12)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x : ℝ} (hx : Real.exp (330 : ℝ) ≤ x) :
    |CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)| ≤
      (9 * (1826923053/200000000000 : ℝ)) * x ^ (-(1 : ℝ)/8) :=
  matched_flat_lambda330 hs.toDirect h hRH hqrh hx

theorem matched_direct_and_flat330_without_cotangent
    (hs : DirectCH2Inputs12)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x : ℝ} (hx : Real.exp (330 : ℝ) ≤ x) :
    (|CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)| ≤
      (1826923053/200000000000 : ℝ) * x ^ (-(1 : ℝ)/8)) ∧
    (|CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)| ≤
      (9 * (1826923053/200000000000 : ℝ)) * x ^ (-(1 : ℝ)/8)) ∧
    ((1826923053/200000000000 : ℝ) * x ^ (-(1 : ℝ)/8) <
      (9 * (1826923053/200000000000 : ℝ)) * x ^ (-(1 : ℝ)/8)) :=
  matched_direct_and_flat330 hs.toDirect h hRH hqrh hx

end LambdaEvolutionA

#print axioms LambdaEvolutionA.DirectCH2Inputs12.toDirect
#print axioms LambdaEvolutionA.direct_lambda330_without_cotangent
#print axioms LambdaEvolutionA.matched_flat_lambda330_without_cotangent
#print axioms LambdaEvolutionA.matched_direct_and_flat330_without_cotangent
