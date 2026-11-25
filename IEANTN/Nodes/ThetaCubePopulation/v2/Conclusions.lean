/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.ThetaCubePopulation.v1.Conclusions
namespace ThetaCubePopulation.v2
open Real
/-- Exact frozen written-discovery coefficient, formally completed posthoc. -/
def cube_density_09669924 : Prop := ∀ n:ℝ, exp 8≤n →
  (2417481/2500000:ℝ)*n^2/log n<((IEANTN.ThetaWindows.openPrimes (n^3) ((n+1)^3)).card:ℝ)
/-- Natural onset for the same strict-open count. -/
def cube_density_09669924_natural : Prop := ∀ n:ℕ, 2981≤n →
  (2417481/2500000:ℝ)*(n:ℝ)^2/log (n:ℝ)<
    ((IEANTN.ThetaWindows.openPrimes ((n:ℝ)^3) (((n:ℝ)+1)^3)).card:ℝ)
/-- Conservative finite-range source consequence covering the exact seam. -/
def finite_seam_098 : Prop := ∀ n:ℝ, exp 8≤n → n≤2154433 →
  (49/50:ℝ)*n^2/log n<((IEANTN.ThetaWindows.openPrimes (n^3) ((n+1)^3)).card:ℝ)
/-- Coefficient comparison only on the common onset; no earlier-onset claim. -/
def strict_gain_on_common_ray : Prop := ∀ n:ℝ, exp 8≤n →
  (193/200:ℝ)*n^2/log n<(2417481/2500000:ℝ)*n^2/log n
/-- The earlier-onset .965 theorem remains an unchanged network dependency. -/
def retains_0965 : Prop := ThetaCubePopulation.v1.cube_density_0965
end ThetaCubePopulation.v2
