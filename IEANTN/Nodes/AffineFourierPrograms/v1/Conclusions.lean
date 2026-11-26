/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.AffineFourierPrograms.v1.Tables
import IEANTN.Vocabulary.AffineFourierWindow
import IEANTN.Vocabulary.CMSFunctional

noncomputable section
open Real MeasureTheory IEANTN.CMSFunctional IEANTN.AffineFourierWindow
namespace AffineFourierPrograms.v1

def sparseWindow : ℝ → ℝ := affineSpectrum sparseNodes 8
def sparseAmplitude : ℝ → ℝ := inverseCosine sparseWindow
def flatWindow : ℝ → ℝ := affineSpectrum flatNodes 8
def flatAmplitude : ℝ → ℝ := inverseCosine flatWindow

/-- The actual sparse16-node numerical program's Fourier witness. The chosen
Solution consumes source parsing, C execution, overflow/error bounds and the
numerical norm result; the mathematical statement fixes the exact input table.
The general norm identity remains an explicitly imported literature input. -/
def sparse_witness : Prop :=
  Eligible sparseAmplitude sparseWindow ∧
  mass sparseAmplitude≤(887721072633027910/1000000000000000000 : ℝ) ∧
  positiveLeak sparseWindow=(119725872611533800/(8*1000000000000000000) : ℝ) ∧
  sparseAmplitude 0=1 ∧
  (∀ v : ℝ, |sparseWindow v|≤(546871713113309800/1000000000000000000 : ℝ)) ∧
  (∃ v : ℝ, |sparseWindow v|=(546871713113309800/1000000000000000000 : ℝ))

/-- The separate constant-window C program instance. Its exact origin value is
15a/8, slightly below1, and is retained rather than silently normalized to1.
The zero leakage and actual attained maximum are mathematically proved. -/
def flat_witness : Prop :=
  Eligible flatAmplitude flatWindow ∧
  mass flatAmplitude≤(1120475208606944546/1000000000000000000 : ℝ) ∧
  positiveLeak flatWindow=0 ∧
  flatAmplitude 0=((15*533333333333333333)/(8*1000000000000000000) : ℝ) ∧
  (∀ v : ℝ, |flatWindow v|≤(533333333333333333/1000000000000000000 : ℝ)) ∧
  (∃ v : ℝ, |flatWindow v|=(533333333333333333/1000000000000000000 : ℝ))
end AffineFourierPrograms.v1
