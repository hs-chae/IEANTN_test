/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerProgramA.Program
namespace PVEvolutionA.Evaluator
open WinnerProgramA LeanCert.Core LeanCert.Engine
/-- The chosen precision is safe only through the same rigorous enclosure checker. -/
def cfg : DyadicConfig := { precision := -100, taylorDepth := 32 }
def runRow (r : Row) : IntervalDyadic × Bool :=
  CH2QRH.DensityComputation.checkedSumAux r.body 0 (r.cells-1) finSumZero
    (LeanCert.Internal.Dyadic.prepareContext cfg)
def run (p : List Row) := p.map runRow

theorem source_linked_upper (p : List Row) (bs : List ℚ)
    (h : acceptUpper (run p) bs = true) : value p ≤ ((bs.sum:ℚ):ℝ) := by
  induction p generalizing bs with
  | nil => cases bs <;> simp_all [run,acceptUpper,value]
  | cons r rs ih =>
    cases bs with
    | nil => simp [run,acceptUpper] at h
    | cons b bs =>
      have hh : (((runRow r).2 && (runRow r).1.upperBoundedBy b)=true) ∧
          (acceptUpper (run rs) bs=true) := by simpa [run,acceptUpper] using h
      have hr : rowValue r≤(b:ℝ) := by
        apply CH2QRH.DensityComputation.verify_upper r.body 0 (r.cells-1) b cfg (by decide)
        exact hh.1
      have ht:=ih bs hh.2
      simp only [value,List.map_cons,List.sum_cons,Rat.cast_add] at *
      linarith
#print axioms source_linked_upper
end PVEvolutionA.Evaluator
