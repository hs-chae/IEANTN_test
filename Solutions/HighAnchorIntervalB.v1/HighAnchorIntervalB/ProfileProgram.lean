/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.ProfileSource
import PVEvolutionA.Recovery.GaussianBasisRun
import WinnerProgramA.Program

namespace HighAnchorIntervalB.Profile
open LeanCert.Core LeanCert.Engine WinnerProgramA
open PVEvolutionA.Recovery
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- One high-anchor row. Its proposed rational caps have no authority until
all eight actual source-expression checks and the arithmetic checker pass. -/
def row : WinnerHeightProfiles.Row := ⟨40,68729633/1000000,311587627677/500000000000,18639224289/500000000000,709097/1000000000000,30441/1000000000000,71651415817/62500000000,1747296791613/250000000000,690401/100000⟩
def slope : ℚ := 556817/100000

/-- The actual eight inherited source expressions, in checker order. -/
def scalarExpr (i : Fin 8) : Expr := ![
  PVEvolutionA.Recovery.Profile.oneExpr row,PVEvolutionA.Recovery.Profile.twoExpr row,
  PVEvolutionA.Recovery.Profile.logExpr row,PVEvolutionA.Recovery.Profile.zeroExpr row,
  PVEvolutionA.Recovery.Profile.residualExpr row,PVEvolutionA.Recovery.Profile.vExpr row,
  PVEvolutionA.Recovery.Profile.kExpr row,PVEvolutionA.Recovery.Profile.bExpr row] i

def scalarTarget (i : Fin 8) : ℚ := ![row.m1,row.m2,row.h,row.r0,row.r1,row.V,row.K,slope] i

def lowerSide (i : Fin 8) : Bool := decide (i.val=2 ∨ i.val=7)

def scalarCheck (i : Fin 8) : Bool :=
  if lowerSide i then checkFinSumLowerBoundFull (scalarExpr i) 0 0 (scalarTarget i) WinnerOriginalScalars.cfg
  else CH2QRH.DensityComputation.checkUpperBound (scalarExpr i) 0 0 (scalarTarget i) WinnerOriginalScalars.cfg

/-- Exact checker execution, with no accuracy or desired-result premise. -/
def run : List Bool := List.ofFn scalarCheck
def Exec (out : List Bool) : Prop := out=run
 theorem execution : Exec run := rfl

/-- Reviewed exact-dyadic executions for the two density-profile operands. -/
def kRow : WinnerProgramA.Row := ⟨PVEvolutionA.Recovery.Profile.kExpr row,1⟩
def bRow : WinnerProgramA.Row := ⟨PVEvolutionA.Recovery.Profile.bExpr row,1⟩
def kProgram : List WinnerProgramA.Row := [kRow]
def bProgram : List WinnerProgramA.Row := [bRow]
def kOutput := WinnerProgramA.run kProgram
def bOutput := WinnerProgramA.run bProgram

theorem k_execution : WinnerProgramA.Exec kProgram kOutput := rfl
theorem b_execution : WinnerProgramA.Exec bProgram bOutput := rfl

def capAccepted : Bool := WinnerProgramA.acceptUpper kOutput [row.K] &&
  WinnerProgramA.acceptLower bOutput [slope]
def accepted : Bool := run.all id && capAccepted

/-- Actual cached evaluator outputs, retained for source/output association. -/
def scalarOutput (i : Fin 8) : IntervalDyadic×Bool :=
  CH2QRH.DensityComputation.checkedSumAux (scalarExpr i) 0 0 finSumZero
    (LeanCert.Internal.Dyadic.prepareContext WinnerOriginalScalars.cfg)

theorem checks_of_accept (h : accepted=true) : PVEvolutionA.Recovery.Profile.ScalarChecks row slope := by
  have h0 : run.all id=true ∧ capAccepted=true := by simpa [accepted,Bool.and_eq_true] using h
  have h := h0.1
  simpa [run,List.ofFn_succ,scalarCheck,scalarExpr,scalarTarget,lowerSide,
    PVEvolutionA.Recovery.Profile.ScalarChecks,Bool.and_eq_true,and_assoc] using h

/-- The source-count consumer receives the result of this exact execution. -/
theorem checks_of_execution (out:List Bool) (hex:Exec out) (hc:(out.all id && capAccepted)=true) :
    PVEvolutionA.Recovery.Profile.ScalarChecks row slope := by
  subst out
  exact checks_of_accept hc

theorem k_value : WinnerProgramA.value kProgram=
    WinnerOriginalScalars.value (PVEvolutionA.Recovery.Profile.kExpr row) := by
  simp [WinnerProgramA.value,kProgram,WinnerProgramA.rowValue,kRow,WinnerOriginalScalars.value]

theorem b_value : WinnerProgramA.value bProgram=
    WinnerOriginalScalars.value (PVEvolutionA.Recovery.Profile.bExpr row) := by
  simp [WinnerProgramA.value,bProgram,WinnerProgramA.rowValue,bRow,WinnerOriginalScalars.value]

end HighAnchorIntervalB.Profile
