/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.PrimeInterval.v4.Conclusions
namespace PrimePowerPopulation.v2
open Real IEANTN.PrimeWindows
/-- Exact whole-cube width of the frozen trial algorithm, normalized at n³. -/
noncomputable def wholeWidth (n:ℝ):ℝ:=((n+1)^3-n^3)/(3*n*sqrt n*log n)
/-- Posthoc formal completion of the frozen E1 trial's exact0.78146 conclusion.
For every REALn>=exp8 the cube interval is strictly open at both endpoints.
The analytic input remains exactly the original optimized strict Octic family. -/
def cube_density_all_real : Prop := ∀ n:ℝ,exp 8≤n →
  (39073/50000:ℝ)*n^2/log n<((primesBetween (n^3) ((n+1)^3)).card:ℝ)
/-- Same unchanged real onset converted to naturaln>=2981. -/
def cube_density_natural : Prop := ∀ n:ℕ,2981≤n →
  (39073/50000:ℝ)*(n:ℝ)^2/log n<((primesBetween ((n:ℝ)^3) (((n:ℝ)+1)^3)).card:ℝ)
/-- Exact single-window branch of the prospective algorithm. -/
def single_window_cube : Prop := ∀ n:ℝ,exp 8≤n →wholeWidth n≤16 →
  (39073/50000:ℝ)*n^2/log n<((primesBetween (n^3) ((n+1)^3)).card:ℝ)
/-- Equal k=ceil(C0/16) full open cells give the stronger0.789 bound whenC0>16. -/
def equal_cell_cube : Prop := ∀ n:ℝ,exp 8≤n →16<wholeWidth n →
  (789/1000:ℝ)*n^2/log n<((primesBetween (n^3) ((n+1)^3)).card:ℝ)
/-- Stronger late margin in the same equal-cell construction, logn>=12. -/
def equal_cell_cube_late : Prop := ∀ n:ℝ,exp 8≤n →16<wholeWidth n →12≤log n →
  (201/250:ℝ)*n^2/log n<((primesBetween (n^3) ((n+1)^3)).card:ℝ)
/-- The original0.7 coefficient is retained on exactly its old real domain. -/
def retains_070_all_real : Prop := ∀ n:ℝ,exp 8≤n →
  (7/10:ℝ)*n^2/log n<((primesBetween (n^3) ((n+1)^3)).card:ℝ)
/-- Strict improvement of the coefficient at the same onset and endpoints. -/
def strict_coefficient_gain : Prop := ∀ n:ℝ,exp 8≤n →
  (7/10:ℝ)*n^2/log n<(39073/50000:ℝ)*n^2/log n
end PrimePowerPopulation.v2
