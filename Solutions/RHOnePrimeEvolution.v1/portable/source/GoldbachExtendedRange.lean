/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PopulationFrontier

/-! A new multiplicity/range tradeoff. The frozen injection takes p>n/2 and
has no loss. Here p>n/3 permits two possible large components per sorted triple,
so the lower count is halved but the admissible finite-Goldbach geometry expands.
No binary Goldbach hypothesis is proved by this transfer. -/
namespace RHOnePrime.Goldbach
open Real Set Finset
open RHOcticPush.Goldbach
set_option maxHeartbeats 0

/-- Sort a finite-Goldbach pair with the chosen prime. This establishes that
the prime is one of the actual sorted triple's components. -/
lemma triple_containing_prime {H n p : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n)
    (hp : p.Prime) (hp2 : 2 < p) (hupper : p + 4 ≤ n)
    (hres : n - p ≤ H) :
    ∃ t ∈ sortedTriples n, p = t.1 ∨ p = t.2.1 ∨ p = t.2.2 := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hm : Even (n - p) := hn.tsub_odd hpodd
  obtain ⟨a, b, ha, hb, hab, hsum⟩ := choose_sorted_pair hEven (by omega) hres hm
  by_cases hpa : p ≤ a
  · refine ⟨(p, a, b), mem_sortedTriples.mpr ⟨hp, ha, hb, hpa, hab, ?_⟩,
      Or.inl rfl⟩
    omega
  · by_cases hpb : p ≤ b
    · refine ⟨(a, p, b), mem_sortedTriples.mpr
        ⟨ha, hp, hb, by omega, hpb, ?_⟩, Or.inr (Or.inl rfl)⟩
      omega
    · refine ⟨(a, b, p), mem_sortedTriples.mpr
        ⟨ha, hb, hp, hab, by omega, ?_⟩, Or.inr (Or.inr rfl)⟩
      omega

/-- If 3p>n then p cannot be the smallest sorted component. Repeated primes
are allowed: counting the union of the two component images remains sound. -/
lemma triple_large_components {H n p : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n)
    (hp : p.Prime) (hp2 : 2 < p) (hthird : n < 3 * p)
    (hupper : p + 4 ≤ n) (hres : n - p ≤ H) :
    ∃ t ∈ sortedTriples n, p = t.2.1 ∨ p = t.2.2 := by
  obtain ⟨t, ht, h⟩ := triple_containing_prime hEven hn hp hp2 hupper hres
  refine ⟨t, ht, ?_⟩
  rcases h with h | h | h
  · have hs := mem_sortedTriples.mp ht
    omega
  · exact Or.inl h
  · exact Or.inr h

/-- Without a size restriction on p, a sorted triple has at most three
distinct candidate components. This reaches the entire finite-input geometry. -/
theorem card_le_three_sortedTriples {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) (s : Finset ℕ)
    (hp : ∀ p ∈ s, p.Prime) (hp2 : ∀ p ∈ s, 2 < p)
    (hupper : ∀ p ∈ s, p + 4 ≤ n) (hres : ∀ p ∈ s, n - p ≤ H) :
    s.card ≤ 3 * (sortedTriples n).card := by
  classical
  have hsub : s ⊆ ((sortedTriples n).image (fun t => t.1) ∪
      (sortedTriples n).image (fun t => t.2.1)) ∪
      (sortedTriples n).image (fun t => t.2.2) := by
    intro p hpS
    obtain ⟨t, ht, h⟩ := triple_containing_prime hEven hn
      (hp p hpS) (hp2 p hpS) (hupper p hpS) (hres p hpS)
    rcases h with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨t, ht, h.symm⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨t, ht, h.symm⟩))
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, ht, h.symm⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le
    ((sortedTriples n).image (fun t => t.1) ∪ (sortedTriples n).image (fun t => t.2.1))
    ((sortedTriples n).image (fun t => t.2.2))
  have h3 := Finset.card_union_le ((sortedTriples n).image (fun t => t.1))
    ((sortedTriples n).image (fun t => t.2.1))
  have ha := Finset.card_image_le (s := sortedTriples n) (f := fun t => t.1)
  have hb := Finset.card_image_le (s := sortedTriples n) (f := fun t => t.2.1)
  have hc := Finset.card_image_le (s := sortedTriples n) (f := fun t => t.2.2)
  omega

theorem window_card_le_three_sortedTriples {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) {u v : ℝ}
    (hu2 : 2 ≤ u) (hupper : v ≤ (n : ℝ) - 4)
    (hres : (n : ℝ) - u ≤ (H : ℝ)) :
    (QuarticWindow.primesBetween u v).card ≤ 3 * (sortedTriples n).card := by
  apply card_le_three_sortedTriples hEven hn
  · intro p hp
    exact (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp
    have h : (2 : ℝ) < p := hu2.trans_lt (Finset.mem_filter.mp hp).2.1
    exact_mod_cast h
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2.2
    have h' : (p : ℝ) + 4 ≤ n := by linarith
    exact_mod_cast h'
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2.1
    have h' : (n : ℝ) ≤ (p : ℝ) + H := by linarith
    have hnat : n ≤ p + H := by exact_mod_cast h'
    omega

theorem card_le_two_sortedTriples {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) (s : Finset ℕ)
    (hp : ∀ p ∈ s, p.Prime) (hp2 : ∀ p ∈ s, 2 < p)
    (hthird : ∀ p ∈ s, n < 3 * p)
    (hupper : ∀ p ∈ s, p + 4 ≤ n) (hres : ∀ p ∈ s, n - p ≤ H) :
    s.card ≤ 2 * (sortedTriples n).card := by
  classical
  have hsub : s ⊆ (sortedTriples n).image (fun t => t.2.1) ∪
      (sortedTriples n).image (fun t => t.2.2) := by
    intro p hpS
    obtain ⟨t, ht, h⟩ := triple_large_components hEven hn
      (hp p hpS) (hp2 p hpS) (hthird p hpS) (hupper p hpS) (hres p hpS)
    rcases h with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, ht, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, ht, h.symm⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((sortedTriples n).image (fun t => t.2.1))
    ((sortedTriples n).image (fun t => t.2.2))
  have h3 := Finset.card_image_le (s := sortedTriples n) (f := fun t => t.2.1)
  have h4 := Finset.card_image_le (s := sortedTriples n) (f := fun t => t.2.2)
  omega

theorem window_card_le_two_sortedTriples {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) {u v : ℝ}
    (hu2 : 2 ≤ u) (hthird : (n : ℝ) / 3 ≤ u)
    (hupper : v ≤ (n : ℝ) - 4) (hres : (n : ℝ) - u ≤ (H : ℝ)) :
    (QuarticWindow.primesBetween u v).card ≤ 2 * (sortedTriples n).card := by
  apply card_le_two_sortedTriples hEven hn
  · intro p hp
    exact (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp
    have h : (2 : ℝ) < p := hu2.trans_lt (Finset.mem_filter.mp hp).2.1
    exact_mod_cast h
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2.1
    have h' : (n : ℝ) < 3 * p := by linarith
    exact_mod_cast h'
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2.2
    have h' : (p : ℝ) + 4 ≤ n := by linarith
    exact_mod_cast h'
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2.1
    have h' : (n : ℝ) ≤ (p : ℝ) + H := by linarith
    have hnat : n ≤ p + H := by exact_mod_cast h'
    omega

/-- The complete frozen four-source octic package is consumed. The new lower
bound works at u=n-H already when 3H≤2n, versus the prior n>2H condition. -/
theorem triples_extended_range
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n)
    (hnH : 3 * H ≤ 2 * n) {C : ℝ}
    (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : C * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    RHOnePrime.Frontier.allowance C ((n : ℝ) - H) / 2 <
      ((sortedTriples n).card : ℝ) := by
  have hcount := RHOcticPush.OptimizedFinal.strict_count_family hG hN hB rh C hC _ hu
  have hnH' : 3 * (H : ℝ) ≤ 2 * n := by exact_mod_cast hnH
  have hcard := window_card_le_two_sortedTriples hEven hn
    (u := (n : ℝ) - H)
    (v := (n : ℝ) - H + C * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H))
    (by linarith [Real.add_one_le_exp (24 : ℝ)])
    (by linarith) (by linarith) (by linarith)
  have hcard' : ((QuarticWindow.primesBetween ((n : ℝ) - H)
      ((n : ℝ) - H + C * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H))).card : ℝ) ≤
      2 * ((sortedTriples n).card : ℝ) := by exact_mod_cast hcard
  unfold RHOnePrime.Frontier.allowance
  linarith

theorem triples_extended_214891875
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n)
    (hnH : 3 * H ≤ 2 * n) (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : (343827 / 160000) * sqrt ((n : ℝ) - H) *
      log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    (1 / 2 + (21 / 10) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
      ((sortedTriples n).card : ℝ) := by
  have h := triples_extended_range hG hN hB rh hEven hn hnH
    (by norm_num : (343827 / 160000 : ℝ) ∈ Icc (103 / 100 : ℝ) 16) hu hwidth
  norm_num [RHOnePrime.Frontier.allowance] at h
  convert h using 1 <;> ring

/-- Full range without n/H ratio restriction. The scalar width budget and
real onset remain necessary and explicit. This does not supply finite binary PV. -/
theorem triples_full_finite_range
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) {C : ℝ}
    (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : C * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    RHOnePrime.Frontier.allowance C ((n : ℝ) - H) / 3 <
      ((sortedTriples n).card : ℝ) := by
  have hcount := RHOcticPush.OptimizedFinal.strict_count_family hG hN hB rh C hC _ hu
  have hcard := window_card_le_three_sortedTriples hEven hn
    (u := (n : ℝ) - H)
    (v := (n : ℝ) - H + C * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H))
    (by linarith [Real.add_one_le_exp (24 : ℝ)]) (by linarith) (by linarith)
  have hcard' : ((QuarticWindow.primesBetween ((n : ℝ) - H)
      ((n : ℝ) - H + C * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H))).card : ℝ) ≤
      3 * ((sortedTriples n).card : ℝ) := by exact_mod_cast hcard
  unfold RHOnePrime.Frontier.allowance
  linarith

theorem triples_full_214891875
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n)
    (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : (343827 / 160000) * sqrt ((n : ℝ) - H) *
      log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    (1 / 3 + (7 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
      ((sortedTriples n).card : ℝ) := by
  have h := triples_full_finite_range hG hN hB rh hEven hn
    (by norm_num : (343827 / 160000 : ℝ) ∈ Icc (103 / 100 : ℝ) 16) hu hwidth
  norm_num [RHOnePrime.Frontier.allowance] at h
  convert h using 1 <;> ring

/-- The full-count generic branch uses closed scalar geometry. Because n is
odd and2H is even, 2H≤n and2H<n give the same admissible integers here; this
restatement contributes no new n-cases. Actual new ranges are the factor2/3
branches. The strict prime-window lower endpoint supplies n<2p. -/
theorem triples_no_loss_range
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n)
    (hnH : 2 * H ≤ n) {C : ℝ}
    (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : C * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    RHOnePrime.Frontier.allowance C ((n : ℝ) - H) <
      ((sortedTriples n).card : ℝ) := by
  have hnH' : 2 * (H : ℝ) ≤ n := by exact_mod_cast hnH
  let u : ℝ := (n : ℝ) - H
  let v : ℝ := u + C * sqrt u * log u
  have hcard : (QuarticWindow.primesBetween u v).card ≤ (sortedTriples n).card := by
    apply card_le_sortedTriples hEven hn
    · intro p hp
      exact (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    · intro p hp
      have hp' := (Finset.mem_filter.mp hp).2.1
      have h : (2 : ℝ) < p := by dsimp [u] at hp'; linarith [Real.add_one_le_exp (24 : ℝ)]
      exact_mod_cast h
    · intro p hp
      have hp' := (Finset.mem_filter.mp hp).2.1
      have h : (n : ℝ) < 2 * p := by dsimp [u] at hp'; linarith
      exact_mod_cast h
    · intro p hp
      have hp' := (Finset.mem_filter.mp hp).2.2
      have h : (p : ℝ) + 4 ≤ n := by dsimp [u, v] at hp'; linarith
      exact_mod_cast h
    · intro p hp
      have hp' := (Finset.mem_filter.mp hp).2.1
      have h : (n : ℝ) ≤ (p : ℝ) + H := by dsimp [u] at hp'; linarith
      have h' : n ≤ p + H := by exact_mod_cast h
      omega
  exact (RHOcticPush.OptimizedFinal.strict_count_family hG hN hB rh C hC _ hu).trans_le
    (by
      change ((QuarticWindow.primesBetween u v).card : ℝ) ≤ ((sortedTriples n).card : ℝ)
      exact_mod_cast hcard)

/-- The range/multiplicity Pareto envelope retains every old no-loss result
and selects the strongest available cardinality transfer at the actual n,H. -/
def multiplicityDivisor (H n : ℕ) : ℕ :=
  if 2 * H ≤ n then 1 else if 3 * H ≤ 2 * n then 2 else 3

theorem triples_piecewise_frontier
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) {C : ℝ}
    (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : C * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    RHOnePrime.Frontier.allowance C ((n : ℝ) - H) / multiplicityDivisor H n <
      ((sortedTriples n).card : ℝ) := by
  unfold multiplicityDivisor
  split_ifs with h1 h2
  · simpa using triples_no_loss_range hG hN hB rh hEven hn h1 hC hu hwidth
  · simpa using triples_extended_range hG hN hB rh hEven hn h2 hC hu hwidth
  · simpa using triples_full_finite_range hG hN hB rh hEven hn hC hu hwidth

/-- The recovered logarithmic slack lowers the finite binary height needed
for a chosen normalized triple target. Both old and new count/width options
remain available; no binary computation is newly assumed verified. -/
theorem triples_shifted_frontier
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n)
    (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) -
      (189 / 40) * sqrt ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    sqrt ((n : ℝ) - H) / multiplicityDivisor H n <
      ((sortedTriples n).card : ℝ) := by
  have hid := RHOnePrime.Frontier.population_one_window_identity hu
  have hwidth' : RHOnePrime.Frontier.populationWidth 1 ((n : ℝ) - H) *
      sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4 := by
    linarith
  have h := triples_piecewise_frontier hG hN hB rh hEven hn
    (RHOnePrime.Frontier.population_one_width_domain hu) hu hwidth'
  have hco : RHOnePrime.Frontier.allowance
      (RHOnePrime.Frontier.populationWidth 1 ((n : ℝ) - H)) ((n : ℝ) - H) =
      sqrt ((n : ℝ) - H) := by
    unfold RHOnePrime.Frontier.allowance RHOnePrime.Frontier.populationWidth
      RHOnePrime.Frontier.widthFor
    ring
  rwa [hco] at h

#print axioms triple_containing_prime
#print axioms triple_large_components
#print axioms card_le_two_sortedTriples
#print axioms card_le_three_sortedTriples
#print axioms window_card_le_two_sortedTriples
#print axioms triples_extended_range
#print axioms triples_extended_214891875
#print axioms triples_full_finite_range
#print axioms triples_full_214891875
#print axioms triples_no_loss_range
#print axioms triples_piecewise_frontier
#print axioms triples_shifted_frontier
end RHOnePrime.Goldbach
