/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteScalarEval
import RamanujanPV.FiniteExpSource
import RamanujanPV.AnalyticTransition

/-! The same actual20-step e source executed in the width-generic scalar
machine used by the logarithm/cell program. This independently fills that model's
callee execution obligation; no initial application representation is assumed. -/
namespace RamanujanPV.FiniteWideExpExecute
open FiniteScalarMachine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def noPrototypes : Prototypes := fun _=>none
def noCalls : Service := fun _ _=>none

theorem low_evaluated : FiniteScalarEval.returnedValue noPrototypes noCalls 200
    FiniteExpSource.lowFunction.body empty=some (word64 3133965575612453533) := by
  decide +kernel

theorem low_source_run : ∃t,Run noPrototypes noCalls FiniteExpSource.lowFunction.body empty
    (.returned t (word64 3133965575612453533)) :=
  FiniteScalarEval.returned_value_sound low_evaluated

#print axioms low_evaluated
#print axioms low_source_run
end RamanujanPV.FiniteWideExpExecute
