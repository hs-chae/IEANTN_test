/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedWinnerA.Envelope
import IEANTN.Nodes.FKS2.v1.Conclusions
import IEANTN.Nodes.FKS2.v3.Conclusions
import IEANTN.Nodes.FKS2.v6.Conclusions
import IEANTN.Nodes.FKS2.v7.Conclusions
import IEANTN.Nodes.FKS2.v9.Conclusions
import IEANTN.Nodes.FKS2Numerics.v1.Conclusions
import IEANTN.Nodes.FKS2Numerics.v5.Conclusions
import IEANTN.Nodes.FKS2Numerics.v6.Conclusions
import IEANTN.Nodes.FKS2Numerics.v7.Conclusions
import IEANTN.Nodes.QRHPropagation.v2.Conclusions
namespace ScopedWinnerA.Comparison
open Real IEANTN
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- These are the actual frozen node propositions, not substitute formulas. -/
def registeredContract : Fin 18 → Prop := ![FKS2.v1.corollary_22,
  FKS2.v1.corollary_23,
  FKS2.v1.corollary_26,
  FKS2.v3.pi_hybrid_22,
  FKS2.v3.pi_hybrid_23,
  FKS2.v3.pi_fks2_rounded,
  FKS2.v6.table4_330,
  FKS2.v7.absolute_pi_bound,
  FKS2.v9.old_absolute_pi,
  FKS2.v9.qrh_absolute_pi,
  FKS2.v9.paired_absolute_pi,
  FKS2Numerics.v1.corollary_22_mid_range,
  FKS2Numerics.v1.corollary_23_mid_range,
  FKS2Numerics.v5.numerical_pi,
  FKS2Numerics.v6.old_pi,
  FKS2Numerics.v7.qrh_pi,
  QRHPropagation.v2.pi_density_300,
  QRHPropagation.v2.classical_three]
theorem absolute_to_normalized {x c : ℝ} (hx : 0<x) (hl : 0<log x)
    (h : |primeCounting x-Li x|≤c*(x/log x)) : Eπ x≤c := by
  exact (div_le_iff₀ (div_pos hx hl)).2 h
/-- Every registered-contract-to-vector correspondence is checked against the imported node type. -/
theorem registered_output_restriction {x : ℝ} (hx : domain x)
    (i : Fin 18) (h : registeredContract i) :
    Eπ x ≤ incumbent x (Fin.castLE (by decide : 18≤37) i) := by
  have hx0 : 0<x := (exp_pos _).trans_le hx.1
  have hlog : 0<log x := by have hh:=(logs hx).1;linarith
  have hx2 : (2:ℝ)≤x := by linarith [add_one_le_exp (330:ℝ),hx.1]
  have hx1 : exp (1:ℝ)≤x := (exp_le_exp.mpr (by norm_num)).trans hx.1
  have hx6 : exp (6:ℝ)≤x := (exp_le_exp.mpr (by norm_num)).trans hx.1
  have hx300 : exp (300:ℝ)≤x := (exp_le_exp.mpr (by norm_num)).trans hx.1
  have hx20000 : x≤exp (20000:ℝ) := hx.2.trans (exp_le_exp.mpr (by norm_num))
  have hquarter : (0.25:ℝ)=1/4 := by norm_num
  have hc3 : (0.00000003:ℝ)=3/100000000 := by norm_num
  have hc16 : (0.00000016:ℝ)=16/100000000 := by norm_num
  have hm0 : margin 0=(1:ℝ) := by norm_num [margin]
  fin_cases i
  · change FKS2.v1.corollary_22 at h
    change Eπ x ≤ (admissibleBound 9.2211 (3/2) 0.84768363 1 x)
    exact h x hx2
  · change FKS2.v1.corollary_23 at h
    change Eπ x ≤ (admissibleBound 0.826 (1/4) 1 5.5666305 x)
    simpa only [hquarter] using h x hx1
  · change FKS2.v1.corollary_26 at h
    change Eπ x ≤ ((0.4298:ℝ))
    exact h x hx2
  · change FKS2.v3.pi_hybrid_22 at h
    change Eπ x ≤ (min (admissibleBound 9.2211 (3/2) 0.84768363 1 x) (admissibleBound (3/100000000) 2 2 1 x))
    have hh := h x hx2
    simpa only [if_pos hx300,hquarter,hc3] using hh
  · change FKS2.v3.pi_hybrid_23 at h
    change Eπ x ≤ (min (admissibleBound 0.826 (1/4) 1 5.5666305 x) (admissibleBound (3/100000000) 2 2 1 x))
    have hh := h x hx1
    simpa only [if_pos hx300,hquarter,hc3] using hh
  · change FKS2.v3.pi_fks2_rounded at h
    change Eπ x ≤ (admissibleBound (16/100000000) 2 2 1 x)
    simpa only [hc16] using h x hx300
  · change FKS2.v6.table4_330 at h
    change Eπ x ≤ ((1.6855e-12:ℝ))
    exact h x hx.1
  · change FKS2.v7.absolute_pi_bound at h
    change Eπ x ≤ (((5:ℝ)/10^16))
    exact absolute_to_normalized hx0 hlog (h x hx.1)
  · change FKS2.v9.old_absolute_pi at h
    change Eπ x ≤ ((1.69e-12:ℝ))
    exact absolute_to_normalized hx0 hlog (h x hx.1)
  · change FKS2.v9.qrh_absolute_pi at h
    change Eπ x ≤ (((5:ℝ)/10^16))
    exact absolute_to_normalized hx0 hlog (h x hx.1)
  · change FKS2.v9.paired_absolute_pi at h
    change Eπ x ≤ (min (1.69e-12:ℝ) ((5:ℝ)/10^16))
    exact le_min (absolute_to_normalized hx0 hlog (h.1 x hx.1))
      (absolute_to_normalized hx0 hlog (h.2 x hx.1))
  · change FKS2Numerics.v1.corollary_22_mid_range at h
    change Eπ x ≤ (admissibleBound 9.2211 (3/2) 0.84768363 1 x)
    simpa only [hm0,one_mul,hquarter] using h x ⟨hx2,hx20000⟩
  · change FKS2Numerics.v1.corollary_23_mid_range at h
    change Eπ x ≤ (admissibleBound 0.826 (1/4) 1 5.5666305 x)
    simpa only [hm0,one_mul,hquarter] using h x ⟨hx6,hx20000⟩
  · change FKS2Numerics.v5.numerical_pi at h
    change Eπ x ≤ (((5:ℝ)/10^16))
    exact h x hx.1
  · change FKS2Numerics.v6.old_pi at h
    change Eπ x ≤ ((1.69e-12:ℝ))
    exact h x hx.1
  · change FKS2Numerics.v7.qrh_pi at h
    change Eπ x ≤ (((5:ℝ)/10^16))
    exact h x hx.1
  · change QRHPropagation.v2.pi_density_300 at h
    change Eπ x ≤ ((0.01323:ℝ)*scale x)
    simpa only [pow_zero,mul_one,scale,show (7/8:ℝ)-1= -(1:ℝ)/8 by norm_num] using h x hx300
  · change QRHPropagation.v2.classical_three at h
    change Eπ x ≤ (admissibleBound (3/100000000) 2 2 1 x)
    simpa only [hc3] using h.2.2 x hx300
#print axioms registered_output_restriction
end ScopedWinnerA.Comparison
