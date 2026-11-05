/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExceptionalDensity
import OriginalBoundaryScalars
namespace WinnerLowerContour
open Real Set Filter Topology WinnerOriginalScalars
set_option maxHeartbeats 0

/-- Move the lower edge down to any selected internal height, even if it is
an exceptional zero ordinate. Only the old analytic expression must be continuous. -/
theorem limit_from_regular_lower_edges {A Hstar H0 : ℝ} {Q : ℝ→ℝ} {E : Set ℝ}
    (hH : Hstar<H0) (hE : E.Countable) (hQ : ContinuousAt Q Hstar)
    (hgood : ∀ u : ℝ, Hstar<u → u<H0 → u∉E → A≤Q u) : A≤Q Hstar := by
  by_contra hn
  have hlt : Q Hstar<A := lt_of_not_ge hn
  have hevent : ∀ᶠ u in 𝓝 Hstar, Q u<A := hQ.eventually (gt_mem_nhds hlt)
  obtain ⟨e,he,hclose⟩ := Metric.eventually_nhds_iff.mp hevent
  have hmin : 0<min e (H0-Hstar) := lt_min he (sub_pos.mpr hH)
  obtain ⟨u,hu,hu',hunot⟩ := WinnerExceptionalDensity.exists_right_not_mem hE Hstar _ hmin
  have hu0 : u<H0 := by have:=min_le_right e (H0-Hstar);linarith
  have hdist : dist u Hstar<e := by
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hu)]
    have:=min_le_left e (H0-Hstar)
    linarith
  exact (not_lt_of_ge (hgood u hu hu0 hunot)) (hclose hdist)

noncomputable def bEightAt (h : ℝ) : ℝ :=
  sqrt ((2+boundaryEta)^2/h^2+((1+2*boundaryEta)/h+1)^2)
noncomputable def bNineAt (gamma h : ℝ) : ℝ :=
  Real.pi/log 2*(log sourceBSeven+log sourceBFive-
    2*log (1-sourceBSix 1000000000 boundaryEta gamma^2))+Real.pi+
    2*(1+2*boundaryEta)/log 2*log (bEightAt h/(2*Real.pi))
noncomputable def cSevenAt (gamma h : ℝ) : ℝ :=
  (2*(1+2*boundaryEta)+2*Real.pi*(1+boundaryEta))/log 2+bNineAt gamma h/log height

theorem cSevenAt_selected (gamma : ℝ) : cSevenAt gamma (height-1)=sourceCSeven gamma := rfl

theorem bEightAt_pos {h : ℝ} (hh : 0<h) : 0<bEightAt h := by
  unfold bEightAt
  apply sqrt_pos.mpr
  have hη : 0<boundaryEta := by norm_num [boundaryEta]
  positivity

theorem bEightAt_antitone {h h' : ℝ} (hh : 0<h) (hle : h≤h') : bEightAt h'≤bEightAt h := by
  have hh' : 0<h' := hh.trans_le hle
  have hη : 0<boundaryEta := by norm_num [boundaryEta]
  unfold bEightAt
  gcongr

/-- The source lower-height parameter enters C7 only through b8 and decreases
as the lower contour rises. Thus C7 at Hstar bounds every nearby H_j above it. -/
theorem cSevenAt_antitone (gamma : ℝ) {h h' : ℝ} (hh : 0<h) (hle : h≤h') :
    cSevenAt gamma h'≤cSevenAt gamma h := by
  have hh' : 0<h' := hh.trans_le hle
  have hH : 0<log height := log_pos (by norm_num [height])
  have hlog2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hη : 0<boundaryEta := by norm_num [boundaryEta]
  have hratio : bEightAt h'/(2*Real.pi)≤bEightAt h/(2*Real.pi) :=
    div_le_div_of_nonneg_right (bEightAt_antitone hh hle) (by positivity)
  have hlog := log_le_log (by positivity [bEightAt_pos hh']) hratio
  have hm := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0≤2*(1+2*boundaryEta)/log 2)
  unfold cSevenAt bNineAt
  gcongr

#print axioms limit_from_regular_lower_edges
#print axioms cSevenAt_antitone
end WinnerLowerContour
