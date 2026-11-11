/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.BoxSound
import FKSComputationLed.CoverProgram
import FKSComputationLed.NativeCells
import FKSComputationLed.RankSound
namespace FKSComputationLed.CoverSound
open Input CoverProgram CellProgram Real

lemma shape_member {xs : List Cell} {U p : Nat}
    (hs : shapeAux U p xs=true) {z : Cell} (hz : z∈xs) :
    p≤z.a ∧ z.a<z.b ∧ z.b≤U := by
  induction xs generalizing p with
  | nil => simp at hz
  | cons a xs ih =>
    simp only [shapeAux,Bool.and_eq_true,decide_eq_true_eq] at hs
    rcases hs with ⟨⟨rfl,hab,hbU⟩,hs⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨le_refl _,hab,hbU⟩
    · obtain ⟨hh,h2,h3⟩ := ih hs hz
      exact ⟨hab.le.trans hh,h2,h3⟩

lemma covered_Ioc {xs : List Cell} {U p : Nat}
    (hs : shapeAux U p xs=true)
    (hc : cellsAux xs (pointInfo p)=true)
    (hr : ∀ z∈xs, Nat.primeCounting z.a=z.ca ∧ Nat.primeCounting z.b=z.cb) :
    ∀ x : ℝ, (p:ℝ)<x → x≤(U:ℝ) →
      |IEANTN.primeCounting x-LiTaylor.Li2 x| ≤ (19/10:ℝ)*sqrt x/log x := by
  induction xs generalizing p with
  | nil =>
    simp only [shapeAux,decide_eq_true_eq] at hs
    intro x hpx hxU
    subst p
    linarith
  | cons a xs ih =>
    simp only [shapeAux,Bool.and_eq_true,decide_eq_true_eq] at hs
    rcases hs with ⟨⟨rfl,hab,hbU⟩,hs⟩
    simp only [cellsAux,Bool.and_eq_true] at hc
    intro x hpx hxU
    by_cases hxb : x≤(a.b:ℝ)
    · obtain ⟨hca,hcb⟩ := hr a (by simp)
      exact BoxSound.cellCheck_sound a hab.le hca hcb hc.1 x hpx.le hxb
    · exact ih hs hc.2 (fun z hz=>hr z (by simp [hz])) x (lt_of_not_ge hxb) hxU

theorem all_counts : ∀ z∈Input.cells.toList,
    Nat.primeCounting z.a=z.ca ∧ Nat.primeCounting z.b=z.cb := by
  have hg := geometry_checked
  simp only [geometryGate,Bool.and_eq_true,decide_eq_true_eq] at hg
  have hc := NativeRanks.all_ranks_checked
  change Input.cells.toList.all (fun z =>
    NativeRanks.rankCheck (Sieve.oddPrimeList NativeRanks.upper) z.a z.ca &&
    NativeRanks.rankCheck (Sieve.oddPrimeList NativeRanks.upper) z.b z.cb)=true at hc
  intro z hz
  obtain ⟨ha,hab,hb⟩ := shape_member hg.2 hz
  have hr := List.all_eq_true.mp hc z hz
  simp only [Bool.and_eq_true] at hr
  constructor
  · exact RankSound.rankCheck_sound (by norm_num [NativeRanks.upper])
      (by dsimp [lower] at ha;omega) (by dsimp [upper] at hb;dsimp [NativeRanks.upper];omega) hr.1
  · exact RankSound.rankCheck_sound (by norm_num [NativeRanks.upper])
      (by dsimp [lower] at ha;omega) (by simpa [upper,NativeRanks.upper] using hb) hr.2

/-- Complete continuous finite PNT, consuming the canonical rank gate and every interval cell.
The two native-assisted numerical leaves are explicit in the printed axiom closure. -/
theorem finite_pnt (x : ℝ) (hx : (100000000:ℝ)≤x) (hxU : x≤1000000000) :
    |IEANTN.primeCounting x-IEANTN.Li x| ≤ (19/10:ℝ)*sqrt x/log x := by
  have hg := geometry_checked
  simp only [geometryGate,Bool.and_eq_true,decide_eq_true_eq] at hg
  have hc := NativeCells.all_cells_checked
  unfold numericGate at hc
  split_ifs at hc with hsize
  · have he : (Input.cells[0]'hsize).a=lower := by
      simpa only [getElem!_pos Input.cells 0 hsize] using hg.1.2
    rw [he] at hc
    change |IEANTN.primeCounting x-LiTaylor.Li2 x|≤_ 
    by_cases hgt : (lower:ℝ)<x
    · exact covered_Ioc hg.2 hc all_counts x hgt hxU
    · have hxe : x=(lower:ℝ) := by dsimp [lower] at hgt ⊢;linarith
      rw [hxe]
      cases hxs : Input.cells.toList with
      | nil =>
        have hh : Input.cells.size=0 := by simpa using congrArg List.length hxs
        omega
      | cons a xs =>
        rw [hxs] at hc
        have hs := hg.2
        rw [hxs] at hs
        simp only [shapeAux,Bool.and_eq_true,decide_eq_true_eq] at hs
        simp only [cellsAux,Bool.and_eq_true] at hc
        obtain ⟨hca,hcb⟩ := all_counts a (by rw [hxs];simp)
        rw [hs.1.1] at hc ⊢
        exact BoxSound.cellCheck_sound a hs.1.2.1.le hca hcb hc.1 _ le_rfl (by exact_mod_cast hs.1.2.1.le)

#print axioms all_counts
#print axioms finite_pnt
end FKSComputationLed.CoverSound
