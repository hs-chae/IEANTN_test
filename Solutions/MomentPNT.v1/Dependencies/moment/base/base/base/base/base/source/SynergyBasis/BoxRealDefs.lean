/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedNumerical.Box
namespace SynergyBasis.RealBox
open ScopedNumerical ScopedNumerical.ProofBox
set_option autoImplicit false
set_option maxHeartbeats 0
/-- Real membership for the same integer endpoints used by the existing
rational proof box. Arithmetic code is reused unchanged; source overflow and
statement execution are distinct obligations. -/
def Contains (p : Nat) (a : ProofBox) (x : ℝ) : Prop :=
  (a.lo:ℝ) ≤ x*(scale p:ℝ) ∧ x*(scale p:ℝ) ≤ (a.hi:ℝ)
end SynergyBasis.RealBox
