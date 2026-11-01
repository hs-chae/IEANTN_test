/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Bridges.QRH.Geometry
import IEANTN.Nodes.ZeroFreeHalfPlane.v1.Conclusions

theorem ZeroFreeHalfPlane.v1.challenge_density_vanishes : ZeroFreeHalfPlane.v1.density_vanishes :=
  fun _ _ _ hβ hσ ↦ QRHGeometry.density_vanishes hβ hσ

theorem ZeroFreeHalfPlane.v1.challenge_classical_region : ZeroFreeHalfPlane.v1.classical_region :=
  fun _ _ _ hβ hR ht hc h ↦ QRHGeometry.classical_region hβ hR ht hc h

theorem ZeroFreeHalfPlane.v1.challenge_reciprocal_differentiable :
    ZeroFreeHalfPlane.v1.reciprocal_differentiable :=
  fun _ h ↦ QRHGeometry.reciprocal_differentiable h
