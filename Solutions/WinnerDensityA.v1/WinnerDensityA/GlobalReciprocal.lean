/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.PiecewiseMoment
namespace WinnerDensityA.Piecewise
open Real Set MeasureTheory Filter Topology CH2QRH
set_option maxHeartbeats 0

/-- The finite partial-summation argument needs integrability, not continuity
of a stepwise count majorant. -/
theorem finite_reciprocal_integrable {α : Type*} (S : Finset α) (γ w : α→ℝ)
    {A T : ℝ} (hA : 0<A) (hAT : A≤T)
    (hγ : ∀ z∈S,A<γ z ∧ γ z≤T) (F : ℝ→ℝ)
    (hi : IntervalIntegrable (fun u=>F u/u^2) volume A T)
    (hc : ∀ u∈Icc A T,(∑z∈S,if γ z≤u then w z else 0)≤F u) :
    (∑z∈S,w z/γ z)≤F T/T+∫u in A..T,F u/u^2 := by
  obtain ⟨hid,hj⟩:=finite_reciprocal_partial_sum S γ w hA hAT hγ
  have hmono:=intervalIntegral.integral_mono_on hAT hj hi (fun u hu=>
    div_le_div_of_nonneg_right (hc u hu) (sq_nonneg u))
  have hsum : (∑z∈S,w z)≤F T := by
    have hh:=hc T ⟨hAT,le_rfl⟩
    simpa only [Finset.sum_congr rfl (fun z hz=>if_pos (hγ z hz).2)] using hh
  rw [hid]
  exact add_le_add (div_le_div_of_nonneg_right hsum (by linarith)) hmono

/-- An infinite integral bounds each actual finite reciprocal sum. This avoids
subtracting a falsely infinite lower tail from a finite-height identity. -/
theorem finite_reciprocal_global {α : Type*} (S : Finset α) (γ w : α→ℝ)
    {A T : ℝ} (hA : 0<A) (hAT : A≤T)
    (hγ : ∀ z∈S,A<γ z ∧ γ z≤T) (F : ℝ→ℝ)
    (hi : IntegrableOn (fun u=>F u/u^2) (Ioi A))
    (hb : Tendsto (fun u=>F u/u) atTop (𝓝 0))
    (hc : ∀ u:ℝ,A≤u→(∑z∈S,if γ z≤u then w z else 0)≤F u) :
    (∑z∈S,w z/γ z)≤∫u in Ioi A,F u/u^2 := by
  have hlim := hb.add (intervalIntegral_tendsto_integral_Ioi A hi tendsto_id)
  simp only [zero_add] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop T] with B hTB
  have hAB := hAT.trans hTB
  have hiB : IntervalIntegrable (fun u=>F u/u^2) volume A B := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB]
    exact hi.mono_set (fun u hu=>hu.1)
  exact finite_reciprocal_integrable S γ w hA hAB
    (fun z hz=>⟨(hγ z hz).1,(hγ z hz).2.trans hTB⟩) F hiB (fun u hu=>hc u hu.1)

#print axioms finite_reciprocal_integrable
#print axioms finite_reciprocal_global
end WinnerDensityA.Piecewise
