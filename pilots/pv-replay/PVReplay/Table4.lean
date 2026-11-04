/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVCore.Bridge
import FKS2Pair.QRHGeometry
import FKS2Pair.OldResult
import IEANTN.Nodes.FKS2Numerics.v6.Conclusions
import IEANTN.Nodes.FKS2Numerics.v7.Conclusions
import IEANTN.Nodes.FKS2.v6.Conclusions
import IEANTN.Nodes.FKS2.v8.Conclusions

/-!
# Table 4, old and QRH, re-derived on the shared contract

Both instances run the selected 30-cell transport program `fks2_table4_transport`: sum the 30
cell literals, multiply by the scale literal, add the anchor, point and tail literals. The
mathematics is the existing one and is not repeated here:

* `FKS2Pair.whole_ray_transport`: `Eπ(x) ≤ Bsafe U` for `x ≥ e^330`, for a valid profile `U`;
* the instance's analytic enclosures of the cells, anchor, point and tail.

The only numerical obligation left is `Bsafe U ≤ scale · Σ xᵢ + anchor + point + tail`, the
application bridge of `PVCore`. Execution, source identity, the loop's error bound and the suffix
rounding come from the shared contract and one certificate per instance.
-/

namespace PVTable4

open Real PVCore

/-- The selected wrapper of every Table 4 transport instance. -/
def program (p : FKS2Table4.TransportProgram) : Program :=
  ⟨"fks2_table4_transport", p.inputs, p.scale, [(.plus, p.anchor), (.plus, p.point), (.plus, p.tail)]⟩

namespace QRH

def program : Program := PVTable4.program FKS2Table4.selected
def source : String := include_str ".." / ".." / ".." / "Solutions" / "FKS2Numerics.v5" / "c" / "fks2_table4_transport.c"

theorem certificate : upperCheck source program (1 / 10 ^ 30) (5 / 10 ^ 16) = true ∧
    (valuesOf program).xs = FKS2Table4.inputValues ∧ (valuesOf program).scale = FKS2Table4.scale ∧
    (valuesOf program).ops = [(.plus, FKS2Table4.anchorUpper), (.plus, FKS2Table4.pointUpper),
      (.plus, FKS2Table4.tailUpper)] := by
  native_decide

theorem bsafe_le : FKS2Pair.Bsafe FKS2Pair.qProfile ≤ ((5 / 10 ^ 16 : ℚ) : ℝ) := by
  apply le_bound_of_check certificate.1
  rw [certificate.2.1, certificate.2.2.1, certificate.2.2.2]
  have h30 : FKS2Pair.qProfile 30 = FKS2Table4.Q 330 := by norm_num [FKS2Pair.qProfile]
  have h0 : FKS2Pair.qProfile 0 = FKS2Table4.Q 300 := by simp [FKS2Pair.qProfile]
  have ha : FKS2Pair.anchor FKS2Pair.qProfile = FKS2Table4.anchor := by
    simp [FKS2Pair.anchor, FKS2Table4.anchor, h0]
  have hc := FKS2Table4.scaled_cells_upper
  have han := FKS2Table4.anchor_upper
  have hp := FKS2Table4.point_upper
  have ht := FKS2Table4.tail_upper
  simp only [FKS2Pair.Bsafe, ha, FKS2Pair.qCells_eq, h30, opsConst, Rat.cast_add, Rat.cast_zero,
    add_zero]
  linarith

/-- `FKS2Numerics.v7.qrh_pi` through the shared contract, from the same two premises as its
challenge. -/
theorem qrh_pi (hpsi : QRHCH2.v5.psi_refined_bound) (hAnchor : FKS2.v6.table4_anchor_300) :
    FKS2Numerics.v7.qrh_pi := by
  intro x hx
  have h := (FKS2Pair.whole_ray_transport (FKS2Pair.qProfile_valid hpsi) hAnchor x hx).trans bsafe_le
  have hb : (((5 / 10 ^ 16 : ℚ)) : ℝ) = (5 : ℝ) / 10 ^ 16 := by norm_num
  rwa [hb] at h

end QRH

namespace Old

def program : Program := PVTable4.program FKS2Pair.Old.oldProgram
def source : String :=
  include_str ".." / ".." / ".." / "Solutions" / "FKS2Numerics.v6" / "c" / "fks2_table4_transport_old.c"

theorem certificate : upperCheck source program (4 / 10 ^ 27) (169 / 10 ^ 14) = true ∧
    (valuesOf program).xs = FKS2Pair.Old.data ∧ (valuesOf program).scale = FKS2Pair.Old.scale ∧
    (valuesOf program).ops = [(.plus, FKS2Pair.Old.anchorUpper), (.plus, FKS2Pair.Old.pointUpper),
      (.plus, FKS2Pair.Old.tailUpper)] := by
  native_decide

theorem bsafe_le : FKS2Pair.Bsafe FKS2Pair.Old.profile ≤ ((169 / 10 ^ 14 : ℚ) : ℝ) := by
  apply le_bound_of_check certificate.1
  rw [certificate.2.1, certificate.2.2.1, certificate.2.2.2]
  have hc := FKS2Pair.Old.scaled_cells_upper
  have han := FKS2Pair.Old.anchor_upper
  have hp := FKS2Pair.Old.point_upper
  have ht := FKS2Pair.Old.tail_upper
  simp only [FKS2Pair.Bsafe, opsConst, Rat.cast_add, Rat.cast_zero, add_zero]
  linarith

/-- `FKS2Numerics.v6.old_pi` through the shared contract, from the same five premises as its
challenge. -/
theorem old_pi (h300 : FKS2.v8.table3_theta_300) (h310 : FKS2.v8.table3_theta_310)
    (h320 : FKS2.v8.table3_theta_320) (h330 : FKS2.v8.table3_theta_330)
    (hAnchor : FKS2.v6.table4_anchor_300) : FKS2Numerics.v6.old_pi := by
  intro x hx
  have h := (FKS2Pair.whole_ray_transport (FKS2Pair.Old.profile_valid h300 h310 h320 h330)
    hAnchor x hx).trans bsafe_le
  have hb : (((169 / 10 ^ 14 : ℚ)) : ℝ) = 1.69e-12 := by norm_num
  rwa [hb] at h

end Old

end PVTable4
