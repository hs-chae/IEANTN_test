/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.GaussianBasisSound
namespace PVEvolutionA.Recovery.GaussianBasis
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Actual evaluation of eighteen fully specified finite Gaussian quadrature rows.
Arb/float proposals have no authority: this exact dyadic checker must accept. -/
theorem accepted : ∀i:Fin 18,
    WinnerProgramA.acceptUpper (output i) [(spec i).cap] = true := by
  native_decide

theorem witness (i : Fin 18) : ∃out, WinnerProgramA.Exec [row i] out ∧
    WinnerProgramA.acceptUpper out [(spec i).cap] = true :=
  ⟨output i,execution i,accepted i⟩

theorem checked_integral (i : Fin 18) :
    (∫y in ((spec i).start:ℝ)..((spec i).start+(spec i).step*cells),
      Gaussian.basis (spec i).n (spec i).k y) ≤ ((spec i).cap:ℝ) :=
  integral_upper i (accepted i)

#print axioms accepted
#print axioms witness
#print axioms checked_integral
end PVEvolutionA.Recovery.GaussianBasis
