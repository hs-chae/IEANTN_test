import SynergyAnalytic.ClosedCount
namespace SynergyAnalytic
open Real Set WinnerOriginalScalars WinnerNewHeightSource
set_option maxHeartbeats 0

noncomputable def continuousMain (d delta j0 j1 j2 sigma T : ℝ) : ℝ :=
  sourceSmoothingR*Real.exp (2*WinnerNewHeightSource.alpha)*Real.log T/(2*Real.pi*d)*
    stripProduct (continuousLeftCap j0 j1 j2 T) (continuousRightCap delta T)
      sigma (rightLine delta T) (d/Real.log T)
noncomputable def continuousSlope (delta j0 j1 j2 T : ℝ) : ℝ :=
  (Real.log (continuousLeftCap j0 j1 j2 T)-Real.log (continuousRightCap delta T))/
    (rightLine delta T-1/2)

theorem continuousMain_centered {d delta j0 j1 j2 sigma beta T : ℝ}
    (hd : 0 < delta) (h0 : 0 ≤ j0) (h1 : 0 ≤ j1) (h2 : 0 ≤ j2) (hT : 1 < T) :
    continuousMain d delta j0 j1 j2 sigma T = continuousMain d delta j0 j1 j2 beta T*
      Real.exp (continuousSlope delta j0 j1 j2 T*(beta-sigma)) := by
  have hl : 0 < Real.log T := Real.log_pos hT
  have hw : (rightLine delta T-(1/2:ℝ)) ≠ 0 := by
    unfold rightLine
    have hh := div_pos hd hl
    linarith
  unfold continuousMain continuousSlope
  rw [stripProduct_centered (continuousLeftCap_pos h0 h1 h2 hT)
    (continuousRightCap_pos hd hT) hw]
  ring

/-- The precise scalar residual checked by each entire height cell. Bounds
on BOTH N(beta,T)'s main term and the interpolation slope are sufficient. -/
theorem continuousMain_cell {d delta j0 j1 j2 sigma beta T c D : ℝ}
    (hd : 0 < d) (hdelta : 0 < delta) (h0 : 0 ≤ j0) (h1 : 0 ≤ j1) (h2 : 0 ≤ j2)
    (hT : 1 < T) (hs : sigma ≤ beta)
    (hc : continuousMain d delta j0 j1 j2 beta T ≤ c)
    (hD : continuousSlope delta j0 j1 j2 T ≤ D) :
    continuousMain d delta j0 j1 j2 sigma T ≤ c*Real.exp (D*(beta-sigma)) := by
  have hl : 0 < Real.log T := Real.log_pos hT
  have hmain : 0 ≤ continuousMain d delta j0 j1 j2 beta T := by
    unfold continuousMain stripProduct WinnerOriginalScalars.sourceSmoothingR
    have hleft := continuousLeftCap_pos h0 h1 h2 hT
    have hright := continuousRightCap_pos hdelta hT
    positivity
  rw [continuousMain_centered hdelta h0 h1 h2 hT]
  exact mul_le_mul hc (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hD (sub_nonneg.mpr hs)))
    (Real.exp_pos _).le (hmain.trans hc)

/-- Actual closed-height zeta count supplied by a certified whole-cell pair.
There is no new density hypothesis or selected future moment premise. -/
theorem height_cell_actual_count {d delta j0 j1 j2 sigma T c D : ℝ}
    (h : PrimaryInputs d delta) (hcaps : UniversalBasisCaps j0 j1 j2)
    (h0 : 0 ≤ j0) (h1 : 0 ≤ j1) (h2 : 0 ≤ j2)
    (hd : (34/100:ℝ) ≤ d) (hdmax : d ≤ 2/5) (hdelta : 0 < delta)
    (hRH : IEANTN.RiemannHypothesisUpTo height)
    (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8) (hT : height ≤ T)
    (hc : continuousMain d delta j0 j1 j2 (7/8) T ≤ c)
    (hD : continuousSlope delta j0 j1 j2 T ≤ D) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _ => (1:ℝ))  ≤ 
      c*Real.exp (D*((7/8)-sigma))+6*Real.log T^2 := by
  have hh := continuous_count_closed h hcaps h0 h1 h2 hd hdmax hdelta hRH hs hs' hT
  have hm := continuousMain_cell (by linarith : 0 < d) hdelta h0 h1 h2
    (lt_of_lt_of_le (by norm_num [height]) hT) hs' hc hD
  exact hh.trans (add_le_add hm le_rfl)

#print axioms continuousMain_centered
#print axioms continuousMain_cell
#print axioms height_cell_actual_count
end SynergyAnalytic
