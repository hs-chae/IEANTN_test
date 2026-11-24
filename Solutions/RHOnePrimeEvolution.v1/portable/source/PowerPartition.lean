/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PowerPopulation
namespace RHOnePrime.PowerPopulation
open Real Set
set_option maxHeartbeats 0

lemma open_primes_subset {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    QuarticWindow.primesBetween a b ⊆ QuarticWindow.primesBetween c d := by
  classical
  intro p hp
  obtain ⟨hpB, hap, hpb⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨?_, hca.trans_lt hap, hpb.trans_le hbd⟩
  exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hpB).1.trans
    (Nat.floor_le_floor hbd), (Nat.mem_primesLE.mp hpB).2⟩

lemma open_count_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (QuarticWindow.primesBetween a b).card + (QuarticWindow.primesBetween b c).card ≤
      (QuarticWindow.primesBetween a c).card := by
  classical
  have hd : Disjoint (QuarticWindow.primesBetween a b) (QuarticWindow.primesBetween b c) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (Finset.mem_filter.mp hp).2.2
    have hq' := (Finset.mem_filter.mp hq).2.1
    linarith
  rw [← Finset.card_union_of_disjoint hd]
  apply Finset.card_le_card
  exact Finset.union_subset (open_primes_subset le_rfl hbc) (open_primes_subset hab le_rfl)

/-- Finite disjoint open cells. Prime endpoints may be omitted, never double counted. -/
theorem tiled_count {a H m : ℝ} (hH : 0 ≤ H) (k : ℕ)
    (hc : ∀ i < k, m < ((QuarticWindow.primesBetween (a + i * H) (a + (i + 1) * H)).card : ℝ)) :
    (k : ℝ) * m ≤ ((QuarticWindow.primesBetween a (a + k * H)).card : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hi := ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))
    have hcell := hc k (Nat.lt_succ_self k)
    have had := open_count_add
      (a := a) (b := a + k * H) (c := a + (k + 1) * H)
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hH)) (by nlinarith)
    have had' : ((QuarticWindow.primesBetween a (a + k * H)).card : ℝ) +
      ((QuarticWindow.primesBetween (a + k * H) (a + (k + 1) * H)).card : ℝ) ≤
        ((QuarticWindow.primesBetween a (a + (k + 1) * H)).card : ℝ) := by exact_mod_cast had
    push_cast
    nlinarith

/-- The positive family count at C=16; a coarse coefficient is retained to
make the disjoint-window lower bound independently inspectable. -/
lemma family_sixteen (hf : OcticFamily) {u : ℝ} (hu : exp 24 ≤ u) :
    13 * sqrt u <
      ((QuarticWindow.primesBetween u (u + 16 * sqrt u * log u)).card : ℝ) := by
  have hu0 : 0 < u := (exp_pos 24).trans_le hu
  have hL : 24 ≤ log u := by simpa using log_le_log (exp_pos 24) hu
  have h := hf 16 (by norm_num) u hu
  have hd : 0 < (21 / 5 : ℝ) / log u := div_pos (by norm_num) (by linarith)
  have hs : 0 < sqrt u := sqrt_pos.mpr hu0
  have hm : 13 * sqrt u < (8 / 9 * 16 - 18203 / 20000 + (21 / 5) / log u) * sqrt u := by
    nlinarith
  exact hm.trans h

#print axioms tiled_count
#print axioms family_sixteen
end RHOnePrime.PowerPopulation
