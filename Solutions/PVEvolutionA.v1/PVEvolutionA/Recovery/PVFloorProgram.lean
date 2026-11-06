/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- Source-linked lower-floor program using evaluator-generated moment lower endpoints. -/
import PVEvolutionA.Recovery.PVFloorModel
namespace PVEvolutionA.Recovery.PVFloor
open Real LeanCert.Core LeanCert.Engine WinnerDensityA WinnerDensityA.Program
set_option maxHeartbeats 0
def boxesAccepted : Prop := ∀ i : Fin cells,
  BoxLower.accepted momentExpr (box i.val) (cap i.val)=true
instance : Decidable boxesAccepted := inferInstanceAs (Decidable (∀ i : Fin cells, _))
def arithmetic : Prop := ∀ i : Fin cells, 0≤cap i.val ∧ cap (i.val+1)≤cap i.val
instance : Decidable arithmetic := inferInstanceAs (Decidable (∀ i : Fin cells, _))

def weightExpr (i : Nat) : Expr :=
  sub (.exp (lit (331*(sigmaQ cells (i+1)-7/8))))
    (.exp (lit (331*(sigmaQ cells i-7/8))))
def program : List WinnerProgramA.Row :=
  ⟨mul (.exp (lit (-331/8))) (lit (cap 0)),1⟩ ::
    (List.range cells).map (fun i => ⟨mul (weightExpr i) (lit (cap i)),1⟩)
def output := WinnerProgramA.run program
def lows (out : List (IntervalDyadic × Bool)) : List ℚ := out.map (fun o => o.1.lo.toRat)
def floor : ℚ := 91369/10000000

def flags (out : List (IntervalDyadic × Bool)) : Bool := out.all (fun o => o.2)
def totalAccepted : Bool := flags output && decide (floor≤(lows output).sum)

theorem accept_own_lows (out : List (IntervalDyadic × Bool)) (h : flags out=true) :
    WinnerProgramA.acceptLower out (lows out)=true := by
  induction out with
  | nil => rfl
  | cons o os ih =>
    have hh : o.2=true ∧ flags os=true := by simpa [flags] using h
    simp only [lows,List.map_cons,WinnerProgramA.acceptLower]
    have hr : o.1.lowerBoundedBy o.1.lo.toRat=true := by
      simp [IntervalDyadic.lowerBoundedBy]
    simp only [hh.1,hr,Bool.true_and]
    simpa only [lows] using ih hh.2

theorem lower_of_execution (h : totalAccepted=true) : (floor:ℝ)≤WinnerProgramA.value program := by
  have hh : flags output=true ∧ floor≤(lows output).sum := by
    simpa only [totalAccepted,Bool.and_eq_true,decide_eq_true_eq] using h
  have hv:=WinnerProgramA.source_linked_lower program output (lows output) rfl
    (accept_own_lows output hh.1)
  exact (Rat.cast_le.mpr hh.2).trans hv
#print axioms moment_semantics
#print axioms moment_le_envelope
#print axioms lower_of_execution
end PVEvolutionA.Recovery.PVFloor
