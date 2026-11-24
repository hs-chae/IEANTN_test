import BoxWindowIdentities
import BoxIntegratedSource
import IEANTN.Nodes.RHSmoothingInputs.v1.Conclusions

/-! General integrated Perron source to the exact ORIGINAL averaged Box EF.
All-zero interchange, both physical boundary terms, the additive-constant
cancellation, the actual log constant, and the complete trivial series are proved.
The genuine general published integrated formula remains an explicit B-tier
literature premise. The conclusion does not acquire an RH assumption. -/
namespace RHOcticPush.BoxPerron
open Real Set MeasureTheory IEANTN.RHSmoothing
set_option maxHeartbeats 0

lemma transported_integrated_source {a b : ℝ} (h : SourceIntegratedPsi)
    (ha : 1 < a) (hab : a ≤ b) :
    transport a b (fun x => (psi1 x:ℂ)) =
      transport a b (fun x : ℝ => (x:ℂ)^2/2) -
      transport a b (fun x => ∑' r,zeroPrimitive x r) -
      transport a b (fun x : ℝ => (x:ℂ)*(Real.log (2*Real.pi):ℂ)) -
      transport a b (fun x => ((∑' n : ℕ,trivialPrimitive n x):ℝ)) := by
  obtain ⟨C,hC⟩ := h
  have hsource : SourceIntegratedPsi := ⟨C,hC⟩
  have hq : ContinuousOn (fun x : ℝ => (x:ℂ)^2/2) (Icc a b) := by fun_prop
  have hz := zeroSum_continuousOn hsource ha hab
  have hl : ContinuousOn (fun x : ℝ => (x:ℂ)*(Real.log (2*Real.pi):ℂ)) (Icc a b) := by
    fun_prop
  have hc : ContinuousOn (fun _x : ℝ => C) (Icc a b) := continuousOn_const
  have ht := trivialSum_continuousOn (b := b) ha
  have he := transport_congr hab (fun x hx => (hC x (ha.trans_le hx.1)).2)
  have h1 := transport_sub (by linarith : 0 < a) hab (((hq.sub hz).sub hl).add hc) ht
  have h2 := transport_add (by linarith : 0 < a) hab ((hq.sub hz).sub hl) hc
  have h3 := transport_sub (by linarith : 0 < a) hab (hq.sub hz) hl
  have h4 := transport_sub (by linarith : 0 < a) hab hq hz
  simp only [Pi.sub_def, Pi.add_def] at h1 h2 h3 h4
  rw [h1,h2,h3,h4,constant_transport (by linarith : 0 < a) hab C,add_zero] at he
  exact he

/-- The exact old Box predicate, derived from a genuine source-general formula.
No RH, Box moment, zero-estimate, packet or numerical result is assumed. -/
theorem box_explicit_formula (h : SourceIntegratedPsi) :
    RHSmoothingInputs.v1.box_explicit_formula := by
  intro L hL s hs
  obtain ⟨ha,hab⟩ := box_window_domain hL hs
  refine ⟨box_zero_summable h hL hs,?_⟩
  have hT := transported_integrated_source h ha hab
  have he : (average box s L:ℂ) = (mainAverage box s L:ℂ) -
      zeroAverage box s L - (Real.log (2*Real.pi):ℂ) + (trivialAverage box s L:ℂ) := by
    rw [←scaled_psi1_transport hL hs,hT]
    simp only [mul_sub]
    rw [scaled_main_transport (by linarith : 0 < L),scaled_zero_sum h hL hs,
      scaled_linear_transport (by linarith : 0 < L),scaled_trivial_transport hL hs]
    ring
  have hr := congrArg Complex.re he
  simpa only [Complex.ofReal_re,Complex.sub_re,Complex.add_re] using hr

theorem box_explicit_formula_from_raw (h : SourceIntegratedPsiRaw) :
    RHSmoothingInputs.v1.box_explicit_formula :=
  box_explicit_formula (integrated_source_normalized h)

#print axioms transported_integrated_source
#print axioms box_explicit_formula
#print axioms box_explicit_formula_from_raw
end RHOcticPush.BoxPerron
