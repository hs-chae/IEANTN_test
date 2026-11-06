/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1Comparison.StepLower
namespace E1Comparison
open Real Set MeasureTheory WinnerDensityA
open PVEvolutionA PVEvolutionA.Recovery PVEvolutionA.Recovery.PVFloor
set_option maxHeartbeats 0
noncomputable def weight (L s:ℝ):ℝ:=L*exp (L*(s-7/8))
theorem weight_nonneg {L s:ℝ} (hL:0 ≤ L):0 ≤ weight L s:=mul_nonneg hL (exp_pos _).le
theorem weight_integral (L a b:ℝ):
    (∫s in a..b,weight L s)=exp (L*(b-7/8))-exp (L*(a-7/8)) := by
  have hd:∀s∈uIcc a b,HasDerivAt (fun t:ℝ=>exp (L*(t-7/8))) (weight L s) s:=by
    intro s _
    convert (((hasDerivAt_id s).sub_const (7/8:ℝ)).const_mul L).exp using 1 <;> dsimp [weight] <;> ring
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable;unfold weight;fun_prop)
theorem weighted_integrable (ha:arithmetic) (L a b:ℝ):
    IntervalIntegrable (fun s=>weight L s*lowerStep s) volume a b := by
  apply (lowerStep_antitone ha).intervalIntegrable.continuousOn_mul
  unfold weight
  fun_prop

theorem mass_le_grid (hb:boxesAccepted) (ha:arithmetic) {n:ℕ} (hn:0<n)
    {L τ:ℝ} (hL:0 ≤ L) (hτ:0<τ):
    exp (L*((3/4:ℝ)-7/8))*lowerStep (3/4)+
      (∫s in (3/4:ℝ)..(7/8:ℝ),weight L s*lowerStep s) ≤
    gridCoefficient (fun s=>SlopedProgram.mathEnvelope s τ) (gradedGrid n) n L := by
  have hz:=graded_zero hn
  have hnlast:=graded_last n
  have hsum:=intervalIntegral.sum_integral_adjacent_intervals
    (a:=gradedGrid n) (n:=n) (fun _ _=>weighted_integrable ha L _ _)
  rw [hz,hnlast] at hsum
  rw [←hsum]
  unfold gridCoefficient
  rw [hz]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (lowerStep_le hb ha ⟨le_rfl,by norm_num⟩ hτ) (exp_pos _).le
  · apply Finset.sum_le_sum
    intro i hi
    have hin:i<n:=Finset.mem_range.mp hi
    have hab:=graded_monotone n (Nat.le_succ i)
    have hdom:gradedGrid n i ∈ Icc (3/4:ℝ) (7/8):=by
      constructor
      · rw [←hz];exact graded_monotone n (Nat.zero_le i)
      · rw [←hnlast];exact graded_monotone n (by omega)
    calc
      _ ≤ ∫s in gradedGrid n i..gradedGrid n (i+1),weight L s*SlopedProgram.mathEnvelope (gradedGrid n i) τ := by
        apply intervalIntegral.integral_mono_on hab (weighted_integrable ha L _ _) (by apply Continuous.intervalIntegrable;unfold weight;fun_prop)
        intro s hs
        exact mul_le_mul_of_nonneg_left
          (((lowerStep_antitone ha) hs.1).trans (lowerStep_le hb ha hdom hτ)) (weight_nonneg hL)
      _ = _ := by rw [intervalIntegral.integral_mul_const,weight_integral]

theorem coarse_le_mass (ha:arithmetic) {L:ℝ} (hL:0 ≤ L):
    StepGrid.weighted (gradedGrid cells) (fun i=>(cap i:ℝ)) cells L ≤
    exp (L*((3/4:ℝ)-7/8))*lowerStep (3/4)+
      (∫s in (3/4:ℝ)..(7/8:ℝ),weight L s*lowerStep s) := by
  have hz:=graded_zero (by decide :0<cells)
  have hnlast:=graded_last cells
  have hsum:=intervalIntegral.sum_integral_adjacent_intervals
    (a:=gradedGrid cells) (n:=cells) (fun _ _=>weighted_integrable ha L _ _)
  rw [hz,hnlast] at hsum
  rw [←hsum]
  unfold StepGrid.weighted
  rw [hz]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
    apply lowerStep_ge (by decide :0<cells)
    rw [←hz];exact graded_monotone cells (by omega)
  · apply Finset.sum_le_sum
    intro j hj
    have hjn:j<cells:=Finset.mem_range.mp hj
    have hab:=graded_monotone cells (Nat.le_succ j)
    calc
      _ = ∫s in gradedGrid cells j..gradedGrid cells (j+1),weight L s*(cap j:ℝ) := by
        rw [intervalIntegral.integral_mul_const,weight_integral]
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on hab (by apply Continuous.intervalIntegrable;unfold weight;fun_prop) (weighted_integrable ha L _ _)
        intro s hs
        exact mul_le_mul_of_nonneg_left (lowerStep_ge hjn hs.2) (weight_nonneg hL)

theorem all_grid_floor (hb:boxesAccepted) (ha:arithmetic) (ht:totalAccepted=true)
    {n:ℕ} (hn:0<n) {L τ:ℝ} (hL:0 ≤ L) (hU:L ≤ 331) (hτ:0<τ):
    (floor:ℝ) ≤ Sloped.coefficient n L τ := by
  have hc:∀i<cells,(cap (i+1):ℝ) ≤ cap i:=by
    intro i hi;exact_mod_cast (ha ⟨i,hi⟩).2
  have hlast:=graded_last cells
  have hmono:=StepGrid.antitone (gradedGrid cells) (fun i=>(cap i:ℝ)) cells
    (fun i hi=>(graded_monotone cells hi).trans_eq hlast) hc hlast hU
  have hp:(floor:ℝ) ≤ StepGrid.weighted (gradedGrid cells) (fun i=>(cap i:ℝ)) cells 331:=by
    rw [←program_semantics];exact lower_of_execution ht
  have hg:=(((hp.trans hmono).trans (coarse_le_mass ha hL)).trans (mass_le_grid hb ha hn hL hτ))
  unfold Sloped.coefficient
  have ht0:0 ≤ exp (-L/8)*((τ+1/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*(τ+1/10^9))+1/10^12:=by positivity
  linarith
#print axioms all_grid_floor
end E1Comparison
