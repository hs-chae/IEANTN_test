/- Copyright (c)2026 IEANTN contributors. Released under Apache2.0. -/
import RectangleAdd
namespace WinnerOldOuter.Rectangles
open Real Set MeasureTheory WinnerOldOuter.Assembly
set_option maxHeartbeats 0

/-- Nested finite intervals for an actual continuous nonnegative integrand. -/
theorem integral_mono_subinterval {f:ℝ→ℝ} {a' a b b':ℝ}
    (ha:a'≤a) (hab:a≤b) (hb:b≤b') (hf:ContinuousOn f (Icc a' b'))
    (hpos:∀x∈Icc a' b',0≤f x) :
    (∫x in a..b,f x)≤∫x in a'..b',f x := by
  have hleft:IntervalIntegrable f volume a' a:=
    (hf.mono (Icc_subset_Icc le_rfl (hab.trans hb))).intervalIntegrable_of_Icc ha
  have hsmall:IntervalIntegrable f volume a b:=
    (hf.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have hright:IntervalIntegrable f volume b b':=
    (hf.mono (Icc_subset_Icc (ha.trans hab) le_rfl)).intervalIntegrable_of_Icc hb
  have hleft0:0≤∫x in a'..a,f x:=intervalIntegral.integral_nonneg ha
    (fun x hx=>hpos x ⟨hx.1,hx.2.trans (hab.trans hb)⟩)
  have hright0:0≤∫x in b..b',f x:=intervalIntegral.integral_nonneg hb
    (fun x hx=>hpos x ⟨(ha.trans hab).trans hx.1,hx.2⟩)
  have he1:=intervalIntegral.integral_add_adjacent_intervals hleft hsmall
  have he2:=intervalIntegral.integral_add_adjacent_intervals (hleft.trans hsmall) hright
  linarith

/-- Pointwise domination on the small rectangle and nonnegativity of G on
the larger rectangle imply domination of the actual full double integrals.
Every section convergence condition follows from the two joint-continuity
hypotheses; no source/comparison/numerical conclusion is assumed. -/
theorem rowIntegral_mono_box {F G:ℝ→ℝ→ℝ} {lo' lo hi hi' a' a b b':ℝ}
    (hlo:lo'≤lo) (hlohi:lo≤hi) (hhi:hi≤hi')
    (ha:a'≤a) (hab:a≤b) (hb:b≤b')
    (hF:ContinuousOn (fun p:ℝ×ℝ=>F p.1 p.2) (Icc lo hi×ˢ Icc a b))
    (hG:ContinuousOn (fun p:ℝ×ℝ=>G p.1 p.2) (Icc lo' hi'×ˢ Icc a' b'))
    (hFG:∀sigma∈Icc lo hi,∀v∈Icc a b,F sigma v≤G sigma v)
    (hGpos:∀sigma∈Icc lo' hi',∀v∈Icc a' b',0≤G sigma v) :
    rowIntegral F lo hi a b≤rowIntegral G lo' hi' a' b' := by
  have hsig:lo'≤hi':=hlo.trans (hlohi.trans hhi)
  have hv:a'≤b':=ha.trans (hab.trans hb)
  have hFswap:ContinuousOn (fun p:ℝ×ℝ=>F p.2 p.1) (Icc a b×ˢ Icc lo hi):=
    hF.comp (continuousOn_snd.prodMk continuousOn_fst) (fun p hp=>⟨hp.2,hp.1⟩)
  have hGswap:ContinuousOn (fun p:ℝ×ℝ=>G p.2 p.1) (Icc a' b'×ˢ Icc lo' hi'):=
    hG.comp (continuousOn_snd.prodMk continuousOn_fst) (fun p hp=>⟨hp.2,hp.1⟩)
  have hFI:ContinuousOn (fun sigma=>∫v in a..b,F sigma v) (Icc lo hi):=
    (rectangle_integrability hab hlohi hFswap).2
  have hGI:ContinuousOn (fun sigma=>∫v in a'..b',G sigma v) (Icc lo' hi'):=
    (rectangle_integrability hv hsig hGswap).2
  have hinner:∀sigma∈Icc lo hi,(∫v in a..b,F sigma v)≤∫v in a'..b',G sigma v:=by
    intro sigma hs
    have hs':sigma∈Icc lo' hi':=⟨hlo.trans hs.1,hs.2.trans hhi⟩
    have hFc:ContinuousOn (F sigma) (Icc a b):=
      hF.comp (continuousOn_const.prodMk continuousOn_id) (fun v hv=>⟨hs,hv⟩)
    have hGc:ContinuousOn (G sigma) (Icc a' b'):=
      hG.comp (continuousOn_const.prodMk continuousOn_id) (fun v hv=>⟨hs',hv⟩)
    have hsmall:=intervalIntegral.integral_mono_on (μ:=volume) hab (hFc.intervalIntegrable_of_Icc hab)
      ((hGc.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab) (hFG sigma hs)
    exact hsmall.trans (integral_mono_subinterval ha hab hb hGc (hGpos sigma hs'))
  have houter:=intervalIntegral.integral_mono_on (μ:=volume) hlohi (hFI.intervalIntegrable_of_Icc hlohi)
    ((hGI.mono (Icc_subset_Icc hlo hhi)).intervalIntegrable_of_Icc hlohi) hinner
  have hwhole:=integral_mono_subinterval hlo hlohi hhi hGI (by
    intro sigma hs
    exact intervalIntegral.integral_nonneg hv (hGpos sigma hs))
  unfold rowIntegral
  exact mul_le_mul_of_nonneg_left (houter.trans hwhole) (by norm_num:(0:ℝ)≤600)
#print axioms rowIntegral_mono_box
end WinnerOldOuter.Rectangles
