/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Configuration
import PVEvolutionA.SlopedGraded
import PVEvolutionA.Evaluator
namespace PVEvolutionA.Controls
open WinnerProgramA
set_option maxHeartbeats 0
/-- Reject invalid generation parameters before calling the interval backend.
The raw backend is not claimed total on division-by-zero expressions. -/
def guarded (n : ℕ) (tau : ℚ) (bs : List ℚ) : Bool :=
  if n=0 then false else if tau≤0 then false else
    acceptUpper (Evaluator.run (gradedProgram 330 tau n)) bs
/-- Actual changed caps/row counts and explicit parameter guards. -/
def originalCases : List (String × Bool × Bool) :=
  [("positive-small",acceptUpper (Evaluator.run (gradedProgram 330 110 32)) [1/1000000,1/10],true),
   ("negative-zero-grid",guarded 0 110 [1,1],false),
   ("negative-undercap",acceptUpper (Evaluator.run (gradedProgram 330 110 32)) [0,0],false),
   ("negative-missing-row",acceptUpper (Evaluator.run (gradedProgram 330 110 32)) [1],false),
   ("negative-extra-row",acceptUpper (Evaluator.run (gradedProgram 330 110 32)) [1,1,1],false),
   ("negative-zero-tau",guarded 32 0 [1,1],false)]
def slopedGuarded (n : ℕ) (tau : ℚ) (bs : List ℚ) : Bool :=
  if n=0 then false else if tau≤0 then false else
    acceptUpper (Evaluator.run (Sloped.program 330 tau n)) bs
/-- Mutations of the actual evolved expression family, in addition to common-shape controls. -/
def slopedCases : List (String × Bool × Bool) :=
  [("positive-sloped",slopedGuarded 32 110 [1/1000000,1/10],true),
   ("negative-sloped-zero-grid",slopedGuarded 0 110 [1,1],false),
   ("negative-sloped-undercap",slopedGuarded 32 110 [0,0],false),
   ("negative-sloped-missing-row",slopedGuarded 32 110 [1],false),
   ("negative-sloped-extra-row",slopedGuarded 32 110 [1,1,1],false),
   ("negative-sloped-zero-tau",slopedGuarded 32 0 [1,1],false)]
def separatedGuarded (n : ℕ) (tau : ℚ) (bs : List ℚ) : Bool :=
  if n=0 then false else if tau≤0 then false else
    acceptUpper (Evaluator.run (Separated.program 330 tau n)) bs
def separatedCases : List (String × Bool × Bool) :=
  [("positive-separated",separatedGuarded 32 100 [1/1000000,1/10],true),
   ("negative-separated-zero-grid",separatedGuarded 0 100 [1,1],false),
   ("negative-separated-undercap",separatedGuarded 32 100 [0,0],false),
   ("negative-separated-missing-row",separatedGuarded 32 100 [1],false),
   ("negative-separated-extra-row",separatedGuarded 32 100 [1,1,1],false),
   ("negative-separated-zero-tau",separatedGuarded 32 0 [1,1],false)]
def cases := originalCases++slopedCases++separatedCases
def accepted : Bool := cases.all fun c=>c.2.1==c.2.2
/-- Auxiliary test evidence, excluded from every prime-bound proof closure. -/
theorem checked : accepted=true := by native_decide
#print axioms checked
end PVEvolutionA.Controls
