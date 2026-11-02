/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.FKS2.v2.Conclusions

namespace FKS2.v3
open Real IEANTN

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def psi_hybrid : Prop :=
  ∀ x ≥ (2), Eψ x ≤ if exp 300 ≤ x then min (admissibleBound 121.096 (3/2) 2 5.5666305 x) (admissibleBound 0.00000003 2 2 1 x) else admissibleBound 121.096 (3/2) 2 5.5666305 x

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def theta_hybrid : Prop :=
  ∀ x ≥ (2), Eθ x ≤ if exp 300 ≤ x then min (admissibleBound 121.0961 (3/2) 2 5.5666305 x) (admissibleBound 0.00000003 2 2 1 x) else admissibleBound 121.0961 (3/2) 2 5.5666305 x

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def pi_hybrid_22 : Prop :=
  ∀ x ≥ (2), Eπ x ≤ if exp 300 ≤ x then min (admissibleBound 9.2211 (3/2) 0.84768363 1 x) (admissibleBound 0.00000003 2 2 1 x) else admissibleBound 9.2211 (3/2) 0.84768363 1 x

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def pi_hybrid_23 : Prop :=
  ∀ x ≥ (exp 1), Eπ x ≤ if exp 300 ≤ x then min (admissibleBound 0.826 (0.25) 1 5.5666305 x) (admissibleBound 0.00000003 2 2 1 x) else admissibleBound 0.826 (0.25) 1 5.5666305 x

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def pi_fks2_rounded : Prop :=
  HasClassicalBound Eπ 0.00000016 2 2 1 (exp 300)

end FKS2.v3
