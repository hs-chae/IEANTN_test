/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
/-!
# Node `FKS2.v9`

Consumers of the paired FKS2 Table 4 programs: the old reconstructed allowance
(`FKS2Numerics.v6.old_pi`) and the QRH allowance (`FKS2Numerics.v7.qrh_pi`), each turned into an
absolute bound on `|π(x) − Li(x)|` on the same ray `x ≥ exp 330`, plus exact comparisons of the two
allowances. Walkthrough (definitions, the 30-cell transport, the program and its certificate):
`docs/qrh/TABLE4_WALKTHROUGH.md`.
-/
namespace FKS2.v9
open Real IEANTN
/-- **Old reconstructed allowance, absolute form.** For every real `x ≥ exp 330`,
`|π(x) − Li(x)| ≤ 1.69·10⁻¹² · x / log x`, with `Li(x) = ∫₂ˣ dt / log t`.

The constant is the certified output of the retrospectively reconstructed old 30-cell program
(`FKS2Numerics.v6.old_pi`, premises: FKS2 Table 3 rows 300–330 and the `exp 300` anchor). It is
**not** FKS2's published Table 4 value `1.6855·10⁻¹²`. -/
def old_absolute_pi : Prop := ∀ x ≥ exp 330,
  |primeCounting x-Li x| ≤ (1.69e-12:ℝ)*(x/log x)
/-- **QRH allowance, absolute form.** For every real `x ≥ exp 330`,
`|π(x) − Li(x)| ≤ 5·10⁻¹⁶ · x / log x`.

Consumes `FKS2Numerics.v7.qrh_pi`, whose premises are the QRH-derived `ψ` bound
`QRHCH2.v5.psi_refined_bound` and the same `exp 300` anchor. Not a best-known bound on this ray: the
existing Phase 2 density route is stronger under additional inputs. -/
def qrh_absolute_pi : Prop := ∀ x ≥ exp 330,
  |primeCounting x-Li x| ≤ ((5:ℝ)/10^16)*(x/log x)
/-- Both absolute bounds together. The proof needs both providers, as AND requirements. -/
def paired_absolute_pi : Prop := old_absolute_pi ∧ qrh_absolute_pi
/-- The QRH allowance is strictly below the reconstructed old allowance. This compares **certified
allowances**, not actual errors. -/
def strict_reconstructed_improvement : Prop := (5:ℝ)/10^16 < 1.69e-12
/-- The QRH allowance is strictly below FKS2's published Table 4 value `1.6855·10⁻¹²` (row 330).
Again a comparison of allowances, not of actual errors. -/
def strict_historical_improvement : Prop := (5:ℝ)/10^16 < 1.6855e-12
/-- Exact allowance ratios: `1.69·10⁻¹² / 5·10⁻¹⁶ = 3380` and `1.6855·10⁻¹² / 5·10⁻¹⁶ = 3371`.
Pure arithmetic; ratios of allowances, not ratios of true errors. -/
def exact_allowance_ratios : Prop :=
  (1.69e-12:ℝ)/((5:ℝ)/10^16)=3380 ∧
  (1.6855e-12:ℝ)/((5:ℝ)/10^16)=3371
end FKS2.v9
