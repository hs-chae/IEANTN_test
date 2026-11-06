/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.PVFloorSound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
namespace E1Comparison
open Real Set MeasureTheory
open PVEvolutionA PVEvolutionA.Recovery PVEvolutionA.Recovery.PVFloor
set_option maxHeartbeats 0
local instance : Nonempty (Fin cells):=⟨⟨0,by decide⟩⟩

theorem partition_cover (a:ℕ→ℝ) (ha:Monotone a) {n:ℕ} (hn:0<n)
    {s:ℝ} (hs:a 0 ≤ s ∧ s ≤ a n):∃j<n,a j ≤ s ∧ s ≤ a (j+1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h:s ≤ a n
    · by_cases hn0:0<n
      · obtain ⟨j,hj,hjs⟩:=ih hn0 ⟨hs.1,h⟩
        exact ⟨j,by omega,hjs⟩
      · have hz:n=0:=by omega
        exact ⟨0,by omega,by simpa [hz] using hs⟩
    · exact ⟨n,by omega,⟨(lt_of_not_ge h).le,hs.2⟩⟩

noncomputable def lowerStep (s:ℝ):ℝ:=
  sSup (Set.range (fun j:Fin cells=>if s ≤ gradedGrid cells (j.val+1) then (cap j.val:ℝ) else 0))
theorem step_bdd (s:ℝ):BddAbove (Set.range (fun j:Fin cells=>
    if s ≤ gradedGrid cells (j.val+1) then (cap j.val:ℝ) else 0)):=
  (Set.finite_range _).bddAbove

theorem cap_nonneg (ha:arithmetic) (j:Fin cells):0 ≤ (cap j.val:ℝ):=by
  exact_mod_cast (ha j).1

theorem lowerStep_antitone (ha:arithmetic):Antitone lowerStep := by
  intro s t hst
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨j,rfl⟩
  have hj:(if s ≤ gradedGrid cells (j.val+1) then (cap j.val:ℝ) else 0) ≤ lowerStep s:=
    le_csSup (step_bdd s) (Set.mem_range_self j)
  by_cases ht:t ≤ gradedGrid cells (j.val+1)
  · have hs:s ≤ gradedGrid cells (j.val+1):=hst.trans ht
    simpa [ht,hs] using hj
  · have hh:0 ≤ (if s ≤ gradedGrid cells (j.val+1) then (cap j.val:ℝ) else 0):=by
      split_ifs <;> first | exact cap_nonneg ha j | rfl
    have h0:0 ≤ lowerStep s:=hh.trans hj
    simpa [ht] using h0

theorem cap_antitone (ha:arithmetic) {i j:ℕ} (hij:i ≤ j) (hj:j<cells):
    (cap j:ℝ) ≤ cap i := by
  induction j,hij using Nat.le_induction with
  | base => rfl
  | succ k hik ih =>
    have hkc:k<cells:=by omega
    have hn:(cap (k+1):ℝ) ≤ cap k:=by exact_mod_cast (ha ⟨k,hkc⟩).2
    exact hn.trans (ih (by omega))

theorem lowerStep_ge {j:ℕ} (hj:j<cells) {s:ℝ} (hs:s ≤ gradedGrid cells (j+1)):
    (cap j:ℝ) ≤ lowerStep s := by
  have h:=le_csSup (step_bdd s) (Set.mem_range_self (⟨j,hj⟩:Fin cells))
  simpa [lowerStep,hs] using h

theorem lowerStep_le (hb:boxesAccepted) (ha:arithmetic) {s τ:ℝ}
    (hs:s ∈ Icc (3/4:ℝ) (7/8)) (hτ:0<τ):lowerStep s ≤ SlopedProgram.mathEnvelope s τ := by
  have hsz:gradedGrid cells 0 ≤ s:=by simpa [graded_zero (by decide :0<cells)] using hs.1
  have hlast:s ≤ gradedGrid cells cells:=by simpa [graded_last] using hs.2
  have hnonneg:0 ≤ SlopedProgram.mathEnvelope s τ:=by
    obtain ⟨k,hk,hks⟩:=partition_cover (gradedGrid cells) (graded_monotone _) (by decide :0<cells) ⟨hsz,hlast⟩
    have hc:0 ≤ (cap k:ℝ):=cap_nonneg ha ⟨k,hk⟩
    exact hc.trans ((box_moment hb k hk (by simpa only [sigmaQ_cast] using hks)).trans
      (moment_le_envelope _ _ hτ))
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨j,rfl⟩
  by_cases h:s ≤ gradedGrid cells (j.val+1)
  · obtain ⟨k,hk,hks⟩:=partition_cover (gradedGrid cells) (graded_monotone _) (by omega :0<j.val+1) ⟨hsz,h⟩
    have hkc:k<cells:=by omega
    have hc: (cap j.val:ℝ) ≤ cap k:=cap_antitone ha (by omega) j.isLt
    simpa [h] using hc.trans ((box_moment hb k hkc (by simpa only [sigmaQ_cast] using hks)).trans
      (moment_le_envelope _ _ hτ))
  · simpa [h] using hnonneg
#print axioms lowerStep_le
end E1Comparison
