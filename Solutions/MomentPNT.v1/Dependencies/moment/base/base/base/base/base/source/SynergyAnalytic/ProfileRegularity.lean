import SynergyAnalytic.ContinuousProfile
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerOriginalScalars WinnerBetaA.ActualObject
open WinnerBetaA.HeightSource WinnerNewHeightSource
set_option maxHeartbeats 0

theorem continuousLeftCap_pos {j0 j1 j2 T : ℝ}
    (h0 : 0  ≤  j0) (h1 : 0  ≤  j1) (h2 : 0  ≤  j2) (hT : 1 < T) :
    0  <  continuousLeftCap j0 j1 j2 T := by
  have hl : 0 < Real.log T := Real.log_pos hT
  have ht : 0 < T := by linarith
  have hm1 := meanOne_nonneg hT
  have hm2 := meanTwo_nonneg hT
  have hg : 0 < gaussianArea := by unfold gaussianArea;positivity
  have hp : 0 < universalPeak := Real.exp_pos _
  unfold continuousLeftCap errorBudget
  positivity

theorem continuousRightCap_pos {delta T : ℝ} (hd : 0 < delta) (hT : 1 < T) :
    0  <  continuousRightCap delta T := by
  have hl : 0 < Real.log T := Real.log_pos hT
  have ht : 0 < T := by linarith
  have hm := source_mzero_pos
  unfold continuousRightCap WinnerBetaA.HeightSource.rightV rightFive rightSix
  positivity

theorem continuousLeftCap_continuousAt (j0 j1 j2 : ℝ) {T : ℝ} (hT : 1 < T) :
    ContinuousAt (continuousLeftCap j0 j1 j2) T := by
  have hl : 0 < Real.log T := Real.log_pos hT
  have ht : 0 < T := by linarith
  have hz : 0 < zetaScale T := by unfold zetaScale;positivity
  unfold continuousLeftCap errorBudget zetaScale meanOne meanTwo
  fun_prop (disch := positivity)

theorem continuousRightCap_continuousAt {delta T : ℝ} (hd : 0 < delta) (hT : 1 < T) :
    ContinuousAt (continuousRightCap delta) T := by
  have hl : 0 < Real.log T := Real.log_pos hT
  have ht : 0 < T := by linarith
  unfold continuousRightCap WinnerBetaA.HeightSource.rightV rightFive rightSix
  fun_prop (disch := positivity)

theorem continuousDensity_continuousAt {d delta j0 j1 j2 sigma T : ℝ}
    (hd : 0 < d) (hdelta : 0 < delta) (h0 : 0 ≤ j0) (h1 : 0 ≤ j1) (h2 : 0 ≤ j2) (hT : 1 < T) :
    ContinuousAt (continuousDensity d delta j0 j1 j2 sigma) T := by
  have hl : 0 < Real.log T := Real.log_pos hT
  have ht : 0 < T := by linarith
  have hleft := continuousLeftCap_pos h0 h1 h2 hT
  have hright := continuousRightCap_pos hdelta hT
  have hwidth : 0  <  rightLine delta T-(1/2:ℝ) := by unfold rightLine;have hq:=div_pos hdelta hl;linarith
  have hLc := continuousLeftCap_continuousAt j0 j1 j2 hT
  have hRc := continuousRightCap_continuousAt hdelta hT
  have hexp1 : ContinuousAt (fun u:ℝ => (rightLine delta u-(sigma-d/Real.log u))/(rightLine delta u-1/2)) T := by
    unfold rightLine
    fun_prop (disch := first | positivity | exact hwidth.ne')
  have hexp2 : ContinuousAt (fun u:ℝ => ((sigma-d/Real.log u)-1/2)/(rightLine delta u-1/2)) T := by
    unfold rightLine
    fun_prop (disch := first | positivity | exact hwidth.ne')
  have hp1 := hLc.rpow hexp1 (Or.inl hleft.ne')
  have hp2 := hRc.rpow hexp2 (Or.inl hright.ne')
  unfold continuousDensity stripProduct
  exact ((((continuousAt_const.mul (continuousAt_log ht.ne')).div_const _).mul (hp1.mul hp2)).add
    (((continuousAt_log ht.ne').pow 2).const_mul 6))


/-- The exceptional-height set is removed by continuity of the explicit
profile. Finite RH is used only at the original height3e12. -/
theorem continuous_count {d delta j0 j1 j2 sigma T : ℝ}
    (h : PrimaryInputs d delta) (hcaps : UniversalBasisCaps j0 j1 j2)
    (h0 : 0 ≤ j0) (h1 : 0 ≤ j1) (h2 : 0 ≤ j2)
    (hd : (34/100:ℝ) ≤ d) (hdmax : d ≤ 2/5) (hdelta : 0 < delta)
    (hRH : IEANTN.RiemannHypothesisUpTo height)
    (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8) (hT : height ≤ T) :
    IEANTN.zetaN' sigma T  ≤  continuousDensity d delta j0 j1 j2 sigma T := by
  obtain ⟨E,hE,hRegular⟩ := (h.toNewInputs (by linarith)).sourceCount hRH sigma hs hs'
  have hT1 : 1 < T := lt_of_lt_of_le (by norm_num [height]) hT
  apply WinnerExceptionalDensity.zetaN_extend hE hT
    (continuousDensity_continuousAt (by linarith) hdelta h0 h1 h2 hT1)
  intro u hu hnot
  exact continuous_count_regular h hcaps hd hdmax hdelta hs hs' hu (hRegular u hu hnot)

#print axioms continuousDensity_continuousAt
#print axioms continuous_count
end SynergyAnalytic
