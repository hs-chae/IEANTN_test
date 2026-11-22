/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RH.v1.Conclusions
import IEANTN.Nodes.RHSmoothing.v1.Conclusions
import IEANTN.Vocabulary.PrimeCounting
import Mathlib.NumberTheory.Chebyshev

/-! Actual psi-to-prime-counting propagation through the literal four-term
Grenie--Molteni primitive. The prime-power correction is retained explicitly;
no desired J-error estimate is assumed as an analytic source input. -/
namespace RHPrimeCounting.v1
open Real IEANTN
/-- Actual integrated psi error, with ordinary prime-power endpoints. -/
noncomputable def primitive (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n:ℝ)*(x-n))-x^2/2
/-- Literal rational-field bound of GM1312.4465v4 Theorem1.1, PDFp3. -/
noncomputable def primitiveEnvelope (x : ℝ) : ℝ :=
  (231/5000:ℝ)*x*sqrt x+(919/500:ℝ)*x+19851/10000+(5097/10000:ℝ)/x
/-- Published RH-conditional primitive estimate. All four source terms are retained. -/
def gm_source : Prop := RH.v1.hypothesis →
  ∀ x : ℝ, 3 ≤ x → |primitive x| ≤ primitiveEnvelope x
/-- Actual Riemann count minus actual ordinary prime count, not a free error parameter. -/
noncomputable def primePowerCorrection (x : ℝ) : ℝ := riemannPrimeCounting x-primeCounting x
/-- Independent lower-height expansion of the actual prime-power correction; the sum is finite. -/
def prime_power_series : Prop := ∀ x : ℝ, 0 < x → primePowerCorrection x =
  ∑' k : ℕ, primeCounting (x^(1/(k+2:ℝ)))/(k+2:ℝ)
/-- Actual prime-power correction is nonnegative on its analytic domain. -/
def prime_power_nonnegative : Prop := ∀ x : ℝ, 0 < x → 0 ≤ primePowerCorrection x
/-- Proved closed transfer correction on the whole real ray x≥exp8. -/
noncomputable def transferCorrection (x : ℝ) : ℝ := 14+(1386/5000:ℝ)*sqrt x/(log x)^2
/-- Radius supplied by a whole-profile psi provider; no scalar replacement of Q is implied. -/
noncomputable def radius (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sqrt x/log x*f (log x)+transferCorrection x
/-- Actual absolute pi-minus-Li upper bound, retaining the li(2) offset and actual Q. -/
noncomputable def absoluteEnvelope (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  radius f x+|li 2-primePowerCorrection x|
/-- Generic actual prime-counting relay, derived from GM rather than assumed. -/
def generic_transfer : Prop := ∀ x : ℝ, exp 8 ≤ x →
  |primeCounting x-li x-(Chebyshev.psi x-x)/log x+primePowerCorrection x| ≤ transferCorrection x
/-- Boxed whole-profile signed band for actual pi-li on x≥exp35, centered at actual -Q. -/
def boxed_signed : Prop := ∀ x : ℝ, exp 35 ≤ x →
  -radius IEANTN.RHSmoothing.fastBound x-primePowerCorrection x ≤ primeCounting x-li x ∧
    primeCounting x-li x ≤ radius IEANTN.RHSmoothing.fastBound x-primePowerCorrection x
/-- Actual pi-minus-offset-Li bound, with explicit prime-power/offset correction. -/
def boxed_absolute : Prop := ∀ x : ℝ, exp 35 ≤ x →
  |primeCounting x-Li x| ≤ absoluteEnvelope IEANTN.RHSmoothing.fastBound x
/-- Matched original B5 provider transported through exactly the same correction. -/
def B5_absolute : Prop := ∀ x : ℝ, exp 35 ≤ x →
  |primeCounting x-Li x| ≤ absoluteEnvelope (IEANTN.RHSmoothing.envelope (831/1000) (287/500)) x
/-- Strict comparison of certified envelopes, not of unknown actual errors. -/
def boxed_strict_gain : Prop := ∀ x : ℝ, exp 35 ≤ x →
  absoluteEnvelope IEANTN.RHSmoothing.fastBound x+(546/1000:ℝ)*sqrt x/log x <
    absoluteEnvelope (IEANTN.RHSmoothing.envelope (831/1000) (287/500)) x
end RHPrimeCounting.v1
