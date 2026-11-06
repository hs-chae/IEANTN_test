/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.Numerical
import PVEvolutionA.Fast

namespace PVEvolutionA.Recovery.Ray
open WinnerProgramA LeanCert.Core LeanCert.Engine
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def sigmaCells : ℕ := 8192
def program := Numerical.program 330 100 sigmaCells
def bounds : List ℚ := [3/1000000000000,9134698997/1000000000000]
def output := PVEvolutionA.Fast.run program

/-- Exact execution of the reviewed Lean AST evaluator, with no accuracy
premise in the execution relation. This is not C or machine execution semantics. -/
def Exec (out : List (IntervalDyadic×Bool)) : Prop := out=PVEvolutionA.Fast.run program

theorem execution : Exec output := rfl
theorem nonempty_execution : ∃out,Exec out := ⟨output,execution⟩

theorem coefficient_of_execution (out : List (IntervalDyadic×Bool)) (hex : Exec out)
    (hc : acceptUpper out bounds=true) :
    Numerical.coefficient sigmaCells 330 100≤(9134699/1000000000:ℝ) := by
  subst out
  have h := PVEvolutionA.Fast.source_linked_upper program bounds hc
  rw [show program=Numerical.program 330 100 sigmaCells from rfl,
    Numerical.program_semantics _ _ (by norm_num [sigmaCells] : 0<sigmaCells) (by norm_num)] at h
  norm_num [bounds] at h ⊢
  exact h

#print axioms coefficient_of_execution
end PVEvolutionA.Recovery.Ray
