/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ThetaWindows
namespace ThetaCubePopulation.v1
open IEANTN.ThetaWindows
/-- Explicit entire-real cube count from refined Schoenfeld theta endpoints.
The single -1 removes a possible prime at the upper endpoint. -/
def schoenfeld_cube_curve : Prop := ∀ n : ℝ, Real.exp 8 ≤ n →
  cubeSchoenfeldLower n ≤ ((openPrimes (n^3) ((n+1)^3)).card:ℝ)
/-- Signed finite Büthe cube curve, for exp8<=n<=2,000,000.
Its upper endpoint(n+1)^3 is still below10^19; it uses both source clauses. -/
def buthe_cube_curve : Prop := ∀ n : ℝ, Real.exp 8 ≤ n → n ≤ 2000000 →
  cubeButheLower n ≤ ((openPrimes (n^3) ((n+1)^3)).card:ℝ)
/-- Source-enriched uniform quantitative cube count; stronger than the inherited
0.7 coefficient at its same real onset, under different explicit source inputs. -/
def cube_density_096 : Prop := ∀ n : ℝ, Real.exp 8 ≤ n →
  (24/25:ℝ)*n^2/Real.log n < ((openPrimes (n^3) ((n+1)^3)).card:ℝ)
/-- Improved coefficient and earlier ALL-REAL onset; strict open at both ends.
The finite lower region uses signed Büthe clauses; the infinite region uses RH
and refined Schoenfeld. This is source-enrichment, not same-premise dominance. -/
def cube_density_0965 : Prop := ∀ n : ℝ, Real.exp 6 ≤ n →
  (193/200:ℝ)*n^2/Real.log n < ((openPrimes (n^3) ((n+1)^3)).card:ℝ)
/-- Historical finite theta input alone, no RH premise, on every real point. -/
def cube_density_0965_finite : Prop := ∀ n : ℝ, Real.exp 6 ≤ n → n ≤ 2000000 →
  (193/200:ℝ)*n^2/Real.log n < ((openPrimes (n^3) ((n+1)^3)).card:ℝ)
/-- Natural-number conversion of the strong real theorem, starting at n=404. -/
def cube_density_0965_natural : Prop := ∀ n : ℕ, 404 ≤ n →
  (193/200:ℝ)*(n:ℝ)^2/Real.log n <
    ((openPrimes ((n:ℝ)^3) (((n:ℝ)+1)^3)).card:ℝ)
/-- Strict coefficient comparison on the inherited old real domain; this does
not claim that the two source-assumption packages imply each other. -/
def improves_old_coefficient : Prop := ∀ n : ℝ, Real.exp 8 ≤ n →
  (7/10:ℝ)*n^2/Real.log n < (193/200:ℝ)*n^2/Real.log n
end ThetaCubePopulation.v1
