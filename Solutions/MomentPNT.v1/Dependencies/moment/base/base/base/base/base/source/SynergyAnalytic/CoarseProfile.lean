import SynergyAnalytic.CoarseCount
import DensityTail
namespace SynergyAnalytic
open Real Set MeasureTheory Filter Topology WinnerOriginalScalars WinnerBetaA.ActualObject
open WinnerBetaA.HeightSource WinnerNewHeightSource WinnerDensitySource CH2QRH
set_option maxHeartbeats 0

theorem coarse_count {d delta A T U V k sigma:ℝ}
    (h:PrimaryInputs d delta) (hd:(34/100:ℝ) ≤ d) (hdmax:d ≤ 2/5) (hdelta:0<delta)
    (hAH:height ≤ A) (hAT:A ≤ T) (hU:0<U) (hV:0<V)
    (hLeft:∀u,A ≤ u→sourceMoment u (1/2) ≤ U*u^((4:ℝ)/3)*Real.log u^3)
    (hRight:WinnerBetaA.HeightSource.rightV (289/500) delta A ≤ V)
    (hK:densityCoefficient (7/8) d delta WinnerNewHeightSource.alpha U V sourceSmoothingR ≤ k)
    (hB:(0:ℝ) ≤ densitySlope delta U V) (hRH:IEANTN.RiemannHypothesisUpTo height)
    (hs:(3/4:ℝ) ≤ sigma) (hs':sigma ≤ 7/8) :
    IEANTN.zetaN' sigma T ≤ WinnerDensityA.poly k 6 sigma T := by
  obtain ⟨E,hE,hRegular⟩ := (h.toNewInputs (by linarith)).sourceCount hRH sigma hs hs'
  have hT1 : 1<T := lt_of_lt_of_le (by norm_num [height]) (hAH.trans hAT)
  apply WinnerExceptionalDensity.zetaN_extend hE hAT (WinnerDensityA.poly_continuous hT1)
  intro u hu hnot
  exact coarse_count_regular h hd hdmax hdelta hAH hu hU hV (hLeft u hu)
    hRight hK hB hs hs' (hRegular u (hAH.trans hu) hnot)

/-- Every coarse-tail ingredient is an actual consequence of the SAME three
basis caps. The remaining scalar inequalities are numerical obligations,
not new density, interpolation, or future-height moment assumptions. -/
theorem coarse_count_from_basis {d delta A T M1 M2 hbar r eps eta j0 j1 j2 U V k sigma:ℝ}
    (h:PrimaryInputs d delta) (hcaps:UniversalBasisCaps j0 j1 j2)
    (hd:(34/100:ℝ) ≤ d) (hdmax:d ≤ 2/5) (hdelta:0<delta)
    (hA:height ≤ A) (hAT:A ≤ T) (hhbar:14 ≤ hbar) (hhA:hbar ≤ Real.log A)
    (he:0<eps) (heta:0<eta) (hM1:meanOne A ≤ M1) (hM2:meanTwo A ≤ M2)
    (hr:(1461/1000:ℝ)/zetaScale A ≤ r) (h0:0 ≤ j0) (h1:0 ≤ j1) (h2:0 ≤ j2)
    (hBudget:uniformBasisBudget A M1 M2 hbar r eps eta j0 j1 j2 ≤ U)
    (hU:0<U) (hV:0<V)
    (hRight:WinnerBetaA.HeightSource.rightV (289/500) delta A ≤ V)
    (hK:densityCoefficient (7/8) d delta WinnerNewHeightSource.alpha U V sourceSmoothingR ≤ k)
    (hB:(0:ℝ) ≤ densitySlope delta U V) (hRH:IEANTN.RiemannHypothesisUpTo height)
    (hs:(3/4:ℝ) ≤ sigma) (hs':sigma ≤ 7/8) :
    IEANTN.zetaN' sigma T ≤ WinnerDensityA.poly k 6 sigma T := by
  apply coarse_count h hd hdmax hdelta hA hAT hU hV _ hRight hK hB hRH hs hs'
  intro u hu
  exact actual_left_uniform_basis h hcaps hA hu hhbar hhA he heta hM1 hM2 hr h0 h1 h2 hBudget

theorem coarse_count_closed {d delta A T U V k sigma:ℝ}
    (h:PrimaryInputs d delta) (hd:(34/100:ℝ) ≤ d) (hdmax:d ≤ 2/5) (hdelta:0<delta)
    (hAH:height ≤ A) (hAT:A ≤ T) (hU:0<U) (hV:0<V)
    (hLeft:∀u,A ≤ u→sourceMoment u (1/2) ≤ U*u^((4:ℝ)/3)*Real.log u^3)
    (hRight:WinnerBetaA.HeightSource.rightV (289/500) delta A ≤ V)
    (hK:densityCoefficient (7/8) d delta WinnerNewHeightSource.alpha U V sourceSmoothingR ≤ k)
    (hB:(0:ℝ) ≤ densitySlope delta U V) (hRH:IEANTN.RiemannHypothesisUpTo height)
    (hs:(3/4:ℝ) ≤ sigma) (hs':sigma ≤ 7/8) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _=>(1:ℝ)) ≤ WinnerDensityA.poly k 6 sigma T := by
  have hT1 : 1<T := lt_of_lt_of_le (by norm_num [height]) (hAH.trans hAT)
  have hlim : Tendsto (WinnerDensityA.poly k 6 sigma) (𝓝[>] T) (𝓝 (WinnerDensityA.poly k 6 sigma T)) :=
    (WinnerDensityA.poly_continuous hT1).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (density_closed_le_open (by linarith) hu).trans
    (coarse_count h hd hdmax hdelta hAH (hAT.trans hu.le) hU hV hLeft hRight hK hB hRH hs hs')

#print axioms coarse_count_from_basis
#print axioms coarse_count_closed
end SynergyAnalytic
