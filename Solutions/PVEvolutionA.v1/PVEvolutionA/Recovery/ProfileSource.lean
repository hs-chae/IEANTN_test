/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.ProfileFormula
import WinnerDensityA.Moment

namespace PVEvolutionA.Recovery.Profile
open Real Set MeasureTheory WinnerOriginalScalars
set_option maxHeartbeats 0

/-- All-height zero count from actual source inputs and interpreted finite
certificates. Finite RH is required only through the original height. -/
theorem count (p : WinnerHeightProfiles.Row) (b : ℚ)
    (ha : Arithmetic p b) (hc : ScalarChecks p b)
    (accepted : ∀j:Fin 18,WinnerProgramA.acceptUpper (GaussianBasis.output j)
      [(GaussianBasis.spec j).cap]=true)
    (h : WinnerNewHeightSource.NewInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo height)
    {sigma T : ℝ} (hs : (3/4:ℝ)≤sigma) (hs' : sigma≤7/8) (hT : anchor p≤T) :
    IEANTN.zetaN' sigma T≤(p.K:ℝ)*exp (-(b:ℝ)*(7/8-sigma))*
      T^(8*(1-sigma)/3)*log T^(5-2*sigma)+6*log T^(2:ℕ) := by
  have hshift : (0:ℝ)≤p.shift := by exact_mod_cast ha.1
  have hU : (0:ℝ)<p.U := by exact_mod_cast ha.2.2.2.2.2.2.2.2.2.2.1
  have hV : (0:ℝ)<p.V := by exact_mod_cast ha.2.2.2.2.2.2.2.2.2.2.2.1
  have hr := closed_upper (vExpr p) p.V hc.2.2.2.2.2.1
  rw [v_semantics] at hr
  have hk := closed_upper (kExpr p) p.K hc.2.2.2.2.2.2.1
  rw [k_semantics p hU hV] at hk
  have hb := closed_lower (bExpr p) b hc.2.2.2.2.2.2.2
  rw [b_semantics] at hb
  exact WinnerNewHeightSource.count_at_anchor h (by norm_num) (by norm_num) (by norm_num)
    (height_le_anchor p hshift) hT hU hV (kernelCertificate p b ha hc accepted) hr
    (by simpa only [WinnerNewHeightSource.alpha] using hk)
    (by simpa only [WinnerDensitySource.densitySlope] using hb) hRH hs hs'

theorem count_closed (p : WinnerHeightProfiles.Row) (b : ℚ)
    (ha : Arithmetic p b) (hc : ScalarChecks p b)
    (accepted : ∀j:Fin 18,WinnerProgramA.acceptUpper (GaussianBasis.output j)
      [(GaussianBasis.spec j).cap]=true)
    (h : WinnerNewHeightSource.NewInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo height)
    {sigma T : ℝ} (hs : (3/4:ℝ)≤sigma) (hs' : sigma≤7/8) (hT : anchor p≤T) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _↦(1:ℝ))≤
      WinnerDensityA.poly ((p.K:ℝ)*exp ((b:ℝ)*(sigma-7/8))) 6 sigma T := by
  have hT1 : 1<T := (anchor_gt_one p (by exact_mod_cast ha.1)).trans_le hT
  have hlim : Filter.Tendsto
      (WinnerDensityA.poly ((p.K:ℝ)*exp ((b:ℝ)*(sigma-7/8))) 6 sigma) (nhdsWithin T (Ioi T))
      (nhds (WinnerDensityA.poly ((p.K:ℝ)*exp ((b:ℝ)*(sigma-7/8))) 6 sigma T)) :=
    (WinnerDensityA.poly_continuous hT1).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hp := count p b ha hc accepted h hRH hs hs' (hT.trans hu.le)
  have he : -(b:ℝ)*(7/8-sigma)=(b:ℝ)*(sigma-7/8) := by ring
  exact (CH2QRH.density_closed_le_open (by linarith) hu).trans
    (by simpa only [WinnerDensityA.poly,he] using hp)

#print axioms count
#print axioms count_closed
end PVEvolutionA.Recovery.Profile
