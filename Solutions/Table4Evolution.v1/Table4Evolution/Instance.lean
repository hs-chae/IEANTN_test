/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.Bounds
import PVCore.Bridge
import PVCore.Chunked
import IEANTN.Nodes.FKS2.v6.Conclusions

/-!
# One theorem for every configuration

`pi_bound` is the whole generic argument: a profile statement (`ProfileOK`), the shared anchor
`FKS2.v6.table4_anchor_300`, and three finite checks (`cellsOK` for the cells, `constOK` for the
anchor, point and tail, the program's own bound) give `Eπ ≤ B` on `x ≥ e^330`. `program_bound` and
`chunked_bound` supply the last check from `PVCore`'s certificates for a single-call or a chunked
program. An instance is then data (partition, literals, constants) plus one certificate that
evaluates all its finite checks at once.
-/

namespace Table4Evolution

open Real IEANTN PVCore

/-- What a θ profile must provide: on `[e^{lo}, ∞)`, `lo ≥ 300`, the allowance `mOf lo·e^{-s·lo}`. -/
def ProfileOK (s : ℚ) (mOf : ℚ → ℚ) : Prop :=
  ∀ lo : ℚ, 300 ≤ lo → 0 ≤ mOf lo ∧
    ∀ t ≥ exp (lo : ℝ), Eθ t ≤ (mOf lo : ℝ) * exp (-((s : ℝ) * lo))

theorem pi_bound {s : ℚ} {k : ℕ} {mOf : ℚ → ℚ} {rest xs : List ℚ} {a p t B : ℚ}
    (hprof : ProfileOK s mOf) (hAnchor : FKS2.v6.table4_anchor_300)
    (hcells : cellsOK s k mOf (300 :: rest) xs = true)
    (hlast : (300 :: rest).getLast (List.cons_ne_nil _ _) = 330)
    (hconst : constOK s (mOf 300) (mOf 330) a p t = true)
    (hB : ((1 / 2 ^ k : ℚ) : ℝ) * (xs.sum : ℝ) + ((a + p + t : ℚ) : ℝ) ≤ B) :
    HasNumericalBound Eπ B (exp 330) := by
  intro x hx
  obtain ⟨hT, hS⟩ := cellsOK_sound s k mOf 300 rest xs hcells
  rw [hlast] at hT
  simp only [Rat.cast_ofNat] at hT
  have hv := cellsOf_valid s mOf hprof k 300 rest xs hcells
  have h0 : Eθ (exp 300) ≤ (mOf 300 : ℝ) * exp (-((s : ℝ) * 300)) := by
    have := (hprof 300 le_rfl).2 (exp 300) (by norm_num)
    simpa using this
  have h330 : ∀ t ≥ exp 330, Eθ t ≤ (mOf 330 : ℝ) * exp (-((s : ℝ) * 330)) := by
    intro t ht
    have := (hprof 330 (by norm_num)).2 t (by norm_num; exact ht)
    simpa using this
  have hm330 : (0 : ℝ) ≤ (mOf 330 : ℝ) * exp (-((s : ℝ) * 330)) := by
    have : (0 : ℝ) ≤ mOf 330 := by exact_mod_cast (hprof 330 (by norm_num)).1
    positivity
  have hw := whole_ray (cellsOf s mOf (300 :: rest)) hT hv h0 hm330 h330 hAnchor x hx
  have hc := constOK_sound hconst
  unfold allowance at hw
  push_cast at hS hB hc
  linarith

/-- The program part of `pi_bound`'s last hypothesis, from a single-call `PVCore` certificate. -/
theorem program_bound {src : String} {prog : Program} {eps B a p t : ℚ} {k : ℕ}
    (h : upperCheck src prog eps B = true) (hscale : (valuesOf prog).scale = 1 / 2 ^ k)
    (hops : (valuesOf prog).ops = [(.plus, a), (.plus, p), (.plus, t)]) :
    ((1 / 2 ^ k : ℚ) : ℝ) * ((valuesOf prog).xs.sum : ℝ) + ((a + p + t : ℚ) : ℝ) ≤ B := by
  apply le_bound_of_check h
  rw [hscale, hops]
  simp only [opsConst]
  push_cast
  linarith

theorem exactTotal_eq (pairs : List (List ℚ × ℚ)) :
    exactTotal pairs = ((pairs.map Prod.fst).flatten).sum := by
  simp [exactTotal, List.sum_flatten, List.map_map, Function.comp_def]

/-- The same for a chunked program; the cells are checked against the concatenated chunks. -/
theorem chunked_bound {src : String} {prog : ChunkedProgram} {eps B a p t : ℚ} {k : ℕ}
    (h : upperCheckChunked src prog eps B = true)
    (hscale : (chunkedValuesOf prog).scale = 1 / 2 ^ k)
    (hops : (chunkedValuesOf prog).ops = [(.plus, a), (.plus, p), (.plus, t)]) :
    ((1 / 2 ^ k : ℚ) : ℝ) *
        ((((chunkedValuesOf prog).pairs.map Prod.fst).flatten.sum : ℚ) : ℝ) +
      ((a + p + t : ℚ) : ℝ) ≤ B := by
  apply le_bound_of_checkChunked h
  rw [hscale, hops, exactTotal_eq]
  simp only [opsConst]
  push_cast
  linarith

end Table4Evolution
