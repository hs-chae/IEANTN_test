/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import RamanujanPV.QRHFullTail

/-! Separate audit of the actual selected proof terms. A source-text occurrence
of a tactic does not determine whether that tactic contributes an axiom to a
particular theorem. The build receipt binds these results to fresh application
objects and the pinned generic Lean/Mathlib dependencies. This is a kernel
dependency audit, not source-first verification of a numerical C program. -/

#check @CH2QRH.density_transfer_proved
#print axioms CH2QRH.density_transfer_proved

#check @QRHPhase2.pi_expansion_phase2
#print axioms QRHPhase2.pi_expansion_phase2

#check @RamanujanPV.QRHClosure.pi144
#print axioms RamanujanPV.QRHClosure.pi144

#check @RamanujanPV.QRHFullTail.pi_two_sided_144
#print axioms RamanujanPV.QRHFullTail.pi_two_sided_144
