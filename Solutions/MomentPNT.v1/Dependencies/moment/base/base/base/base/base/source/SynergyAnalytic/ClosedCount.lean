import SynergyAnalytic.ProfileRegularity
import DensityTail
namespace SynergyAnalytic
open Real Set MeasureTheory Filter Topology WinnerOriginalScalars WinnerNewHeightSource CH2QRH
set_option maxHeartbeats 0

/-- The actual zero count includes its upper-height endpoint. It is derived
from the original open count by a right limit, without changing finite RH. -/
theorem continuous_count_closed {d delta j0 j1 j2 sigma T : ℝ}
    (h : PrimaryInputs d delta) (hcaps : UniversalBasisCaps j0 j1 j2)
    (h0 : 0 ≤ j0) (h1 : 0 ≤ j1) (h2 : 0 ≤ j2)
    (hd : (34/100:ℝ) ≤ d) (hdmax : d ≤ 2/5) (hdelta : 0 < delta)
    (hRH : IEANTN.RiemannHypothesisUpTo height)
    (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8) (hT : height ≤ T) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _ => (1:ℝ)) ≤
      continuousDensity d delta j0 j1 j2 sigma T := by
  have hT1 : 1<T := lt_of_lt_of_le (by norm_num [height]) hT
  have hlim : Tendsto (continuousDensity d delta j0 j1 j2 sigma) (𝓝[>] T)
      (𝓝 (continuousDensity d delta j0 j1 j2 sigma T)) :=
    (continuousDensity_continuousAt (by linarith) hdelta h0 h1 h2 hT1).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hc := continuous_count h hcaps h0 h1 h2 hd hdmax hdelta hRH hs hs' (hT.trans hu.le)
  exact (density_closed_le_open (by linarith [hT]) hu).trans hc

#print axioms continuous_count_closed
end SynergyAnalytic
