/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalA.ProfileProgram
import WinnerDensityA.HeightPrimary
namespace HighAnchorIntervalA.Profile
open Real Set MeasureTheory PVEvolutionA.Recovery Filter Topology
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem arithmetic : PVEvolutionA.Recovery.Profile.Arithmetic row slope := by native_decide
theorem checked : accepted=true := by native_decide
theorem scalar_checks : PVEvolutionA.Recovery.Profile.ScalarChecks row slope :=
  checks_of_execution run execution checked

theorem k_checked : WinnerProgramA.acceptUpper kOutput [row.K]=true := by
  have hc : run.all id=true ∧
      (WinnerProgramA.acceptUpper kOutput [row.K]=true ∧ WinnerProgramA.acceptLower bOutput [slope]=true) := by
    simpa [accepted,capAccepted,Bool.and_eq_true] using checked
  exact hc.2.1

theorem b_checked : WinnerProgramA.acceptLower bOutput [slope]=true := by
  have hc : run.all id=true ∧
      (WinnerProgramA.acceptUpper kOutput [row.K]=true ∧ WinnerProgramA.acceptLower bOutput [slope]=true) := by
    simpa [accepted,capAccepted,Bool.and_eq_true] using checked
  exact hc.2.2

theorem K_bound : WinnerOriginalScalars.value (PVEvolutionA.Recovery.Profile.kExpr row)≤(row.K:ℝ) := by
  have hp := WinnerProgramA.source_linked_upper kProgram kOutput [row.K] k_execution k_checked
  rw [k_value] at hp
  simpa only [List.sum_cons,List.sum_nil,add_zero] using hp

theorem B_bound : (slope:ℝ)≤WinnerOriginalScalars.value (PVEvolutionA.Recovery.Profile.bExpr row) := by
  have hp := WinnerProgramA.source_linked_lower bProgram bOutput [slope] b_execution b_checked
  rw [b_value] at hp
  simpa only [List.sum_cons,List.sum_nil,add_zero] using hp

/-- The actual upper/lower program results are consumed by the source count. -/
theorem source_count
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {sigma T:ℝ} (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8)
    (hT:WinnerOriginalScalars.height*exp (40:ℝ)≤T) :
    IEANTN.zetaN' sigma T≤(row.K:ℝ)*exp (-(slope:ℝ)*(7/8-sigma))*
      T^(8*(1-sigma)/3)*log T^(5-2*sigma)+6*log T^(2:ℕ) := by
  have hshift : (0:ℝ)≤row.shift := by norm_num [row]
  have hU : (0:ℝ)<row.U := by norm_num [row]
  have hV : (0:ℝ)<row.V := by norm_num [row]
  have hr := WinnerOriginalScalars.closed_upper (PVEvolutionA.Recovery.Profile.vExpr row)
    row.V scalar_checks.2.2.2.2.2.1
  rw [PVEvolutionA.Recovery.Profile.v_semantics] at hr
  have hk := K_bound
  rw [PVEvolutionA.Recovery.Profile.k_semantics row hU hV] at hk
  have hb := B_bound
  rw [PVEvolutionA.Recovery.Profile.b_semantics] at hb
  exact WinnerNewHeightSource.count_at_anchor (h.toNewInputs (by norm_num))
    (by norm_num) (by norm_num) (by norm_num)
    (PVEvolutionA.Recovery.Profile.height_le_anchor row hshift)
    (by simpa [PVEvolutionA.Recovery.Profile.anchor,row] using hT) hU hV
    (PVEvolutionA.Recovery.Profile.kernelCertificate row slope arithmetic scalar_checks GaussianBasis.accepted)
    hr (by simpa only [WinnerNewHeightSource.alpha] using hk)
    (by simpa only [WinnerDensitySource.densitySlope] using hb) hRH hs hs'

/-- Actual zero count under the original source package above the newanchor.
FiniteRH remains at3e12. No source accuracy premise is introduced. -/
theorem source_count_closed
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {sigma T:ℝ} (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8)
    (hT:WinnerOriginalScalars.height*exp (40:ℝ)≤T) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _↦(1:ℝ))≤
      WinnerDensityA.poly ((690401/100000:ℝ)*exp ((556817/100000:ℝ)*(sigma-7/8))) 6 sigma T := by
  have hT1 : 1<T :=
    (PVEvolutionA.Recovery.Profile.anchor_gt_one row (by norm_num [row])).trans_le
      (by simpa [PVEvolutionA.Recovery.Profile.anchor,row] using hT)
  have hlim : Filter.Tendsto
      (WinnerDensityA.poly ((row.K:ℝ)*exp ((slope:ℝ)*(sigma-7/8))) 6 sigma)
      (nhdsWithin T (Ioi T))
      (nhds (WinnerDensityA.poly ((row.K:ℝ)*exp ((slope:ℝ)*(sigma-7/8))) 6 sigma T)) :=
    (WinnerDensityA.poly_continuous hT1).tendsto.mono_left nhdsWithin_le_nhds
  have hclosed : IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _↦(1:ℝ))≤
      WinnerDensityA.poly ((row.K:ℝ)*exp ((slope:ℝ)*(sigma-7/8))) 6 sigma T := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hp := source_count h hRH hs hs' (hT.trans ht.le)
    have he : -(slope:ℝ)*(7/8-sigma)=(slope:ℝ)*(sigma-7/8) := by ring
    exact (CH2QRH.density_closed_le_open (by linarith) ht).trans
      (by simpa only [WinnerDensityA.poly,he] using hp)
  simpa only [row,slope,Rat.cast_div,Rat.cast_ofNat] using hclosed

#print axioms arithmetic
#print axioms checked
#print axioms K_bound
#print axioms B_bound
#print axioms source_count_closed
end HighAnchorIntervalA.Profile
