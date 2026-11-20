/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.Intervals
import RamanujanPV.AnalyticTransition

/-! Exact coverage and mathematical assembly. A theorem in this file is not evidence that a
source execution exists: that obligation is the explicit, structurally checked certificate input. -/
namespace RamanujanPV
open Real IEANTN

/-- Consecutive half-open cells cover [start,stop). Adjacency is equality of integers,
so neither floating-point agreement nor sampled coverage is accepted. -/
inductive CellChain : ℕ → ℕ → List Cell → Prop where
  | nil (n : ℕ) : CellChain n n []
  | cons (c : Cell) {stop : ℕ} {cs : List Cell}
      (rest : CellChain (c.m + 1) stop cs) : CellChain c.n stop (c :: cs)

theorem CellChain.covers {start stop : ℕ} {cs : List Cell}
    (chain : CellChain start stop cs) {x : ℝ}
    (hx : (start : ℝ) ≤ x) (hxstop : x < (stop : ℝ)) :
    ∃ c ∈ cs, (c.n : ℝ) ≤ x ∧ x < (c.m : ℝ) + 1 := by
  induction chain with
  | nil n => exact (not_lt_of_ge hx hxstop).elim
  | @cons c stop cs rest ih =>
    by_cases hc : x < (c.m : ℝ) + 1
    · exact ⟨c, List.mem_cons_self, hx, hc⟩
    · have hnext : ((c.m + 1 : ℕ) : ℝ) ≤ x := by
        push_neg at hc
        exact_mod_cast hc
      obtain ⟨d, hd, hn, hm⟩ := ih hnext hxstop
      exact ⟨d, List.mem_cons_of_mem c hd, hn, hm⟩

/-- This is the exact contract the source-first C checker must establish. Its counts and
transcendental enclosures are obligations; the record's existence is not postulated as an axiom. -/
def CompleteCertificate (start stop : ℕ) (cs : List Cell) : Prop :=
  CellChain start stop cs ∧
    ∀ c ∈ cs, c.FixedPredicate ∧ c.CountsCorrect ∧ c.Enclosures

theorem complete_certificate_sound {start stop : ℕ} {cs : List Cell}
    (certificate : CompleteCertificate start stop cs) :
    ∀ x : ℝ, (start : ℝ) ≤ x → x < (stop : ℝ) → Holds x := by
  intro x hx hs
  obtain ⟨c, hc, hn, hm⟩ := certificate.1.covers hx hs
  obtain ⟨hnumeric, hcounts, henclose⟩ := certificate.2 c hc
  exact fixed_cell_sound c hnumeric hcounts henclose hn hm

/-- An analytic interval is consumed through actual pi upper/lower estimates and a scalar
comparison. This theorem never assumes the actual Ramanujan difference has the desired sign. -/
theorem analytic_sandwich_sound {a b : ℝ} {upper lower : ℝ → ℝ}
    (ha : exp 1 ≤ a)
    (hupper : ∀ x, a ≤ x → x ≤ b → primeCounting x ≤ upper x)
    (hlower : ∀ x, a ≤ x → x ≤ b → lower x ≤ primeCounting (x / exp 1))
    (hcompare : ∀ x, a ≤ x → x ≤ b →
      upper x ^ 2 < exp 1 * x / log x * lower x) :
    ∀ x, a ≤ x → x ≤ b → Holds x := by
  intro x hx hb
  have hx0 : 0 < x := (exp_pos 1).trans_le (ha.trans hx)
  have hl : 0 < log x := by
    have : (1 : ℝ) ≤ log x := by
      simpa using log_le_log (exp_pos 1) (ha.trans hx)
    linarith
  have hu := hupper x hx hb
  have hu0 : 0 ≤ upper x := (primeCounting_nonneg x).trans hu
  unfold Holds
  calc
    primeCounting x ^ 2 ≤ upper x ^ 2 := pow_le_pow_left₀ (primeCounting_nonneg x) hu 2
    _ < exp 1 * x / log x * lower x := hcompare x hx hb
    _ ≤ exp 1 * x / log x * primeCounting (x / exp 1) :=
      mul_le_mul_of_nonneg_left (hlower x hx hb) (by positivity)

/-- Final all-real-ray assembly. The finite segment comes from exact certificate objects,
not from an assumption that the desired finite inequality already holds. The two analytic
segments similarly consume explicit prime-count sandwiches and their scalar deductions. -/
theorem final_ray_from_certificate_and_sandwiches
    {start stop : ℕ} {cs : List Cell} {cut : ℝ}
    {midUpper midLower tailUpper tailLower : ℝ → ℝ}
    (certificate : CompleteCertificate start stop cs)
    (hstop : exp 1 ≤ (stop : ℝ)) (hcut : (stop : ℝ) ≤ cut)
    (midU : ∀ x, (stop : ℝ) ≤ x → x ≤ cut → primeCounting x ≤ midUpper x)
    (midL : ∀ x, (stop : ℝ) ≤ x → x ≤ cut → midLower x ≤ primeCounting (x / exp 1))
    (midScalar : ∀ x, (stop : ℝ) ≤ x → x ≤ cut →
      midUpper x ^ 2 < exp 1 * x / log x * midLower x)
    (tailU : ∀ x, cut ≤ x → primeCounting x ≤ tailUpper x)
    (tailL : ∀ x, cut ≤ x → tailLower x ≤ primeCounting (x / exp 1))
    (tailScalar : ∀ x, cut ≤ x →
      tailUpper x ^ 2 < exp 1 * x / log x * tailLower x) :
    ∀ x : ℝ, (start : ℝ) ≤ x → Holds x := by
  intro x hx
  by_cases hs : x < (stop : ℝ)
  · exact complete_certificate_sound certificate x hx hs
  · have hs' : (stop : ℝ) ≤ x := le_of_not_gt hs
    by_cases hc : x ≤ cut
    · exact analytic_sandwich_sound hstop midU midL midScalar x hs' hc
    · have hcx : cut ≤ x := (lt_of_not_ge hc).le
      exact analytic_sandwich_sound (hstop.trans hcut)
        (fun t ht _ => tailU t ht) (fun t ht _ => tailL t ht)
        (fun t ht _ => tailScalar t ht) x hcx le_rfl

/-- The public endpoint, specialized without changing the genuine source-proof obligation. -/
theorem ramanujan_from_38358837683
    {stop : ℕ} {cs : List Cell} {upper lower : ℝ → ℝ}
    (certificate : CompleteCertificate 38358837683 stop cs)
    (hstop : exp 1 ≤ (stop : ℝ))
    (hu : ∀ x, (stop : ℝ) ≤ x → primeCounting x ≤ upper x)
    (hl : ∀ x, (stop : ℝ) ≤ x → lower x ≤ primeCounting (x / exp 1))
    (hs : ∀ x, (stop : ℝ) ≤ x → upper x ^ 2 < exp 1 * x / log x * lower x) :
    ∀ x : ℝ, 38358837683 ≤ x →
      primeCounting x ^ 2 < exp 1 * x / log x * primeCounting (x / exp 1) := by
  intro x hx
  by_cases h : x < (stop : ℝ)
  · exact complete_certificate_sound certificate x (by exact_mod_cast hx) h
  · have hle : (stop : ℝ) ≤ x := le_of_not_gt h
    exact analytic_sandwich_sound hstop (fun t ht _ => hu t ht)
      (fun t ht _ => hl t ht) (fun t ht _ => hs t ht) x hle le_rfl

#print axioms complete_certificate_sound
#print axioms final_ray_from_certificate_and_sandwiches
#print axioms ramanujan_from_38358837683
end RamanujanPV

namespace RamanujanPV
open Real IEANTN
open RamanujanPV.AnalyticTransition

lemma exp43_le_1e19 : exp (43 : ℝ) ≤ 10000000000000000000 := by
  have he1 : exp 1 ≤ (68 / 25 : ℝ) := by linarith [exp_one_lt_d9]
  have hpow := pow_le_pow_left₀ (exp_pos 1).le he1 43
  have he43 : exp (43 : ℝ) ≤ (68 / 25 : ℝ)^43 := by
    convert! hpow using 1 <;> norm_num [← exp_nat_mul]
  exact he43.trans (by norm_num)

/-- Complete mathematical interval stitching. The finite premise is an exact
checker/count/enclosure contract, never the desired finite positivity. The
`hpi144` argument is an explicitly UNDISCHARGED derived IEANTN conclusion,
not an additional published analytic input. A final QRH theorem must supply it
from the original16 analytic inputs using a fresh checked adapter. Likewise this
assembly does not assert that a source-first execution certificate exists. -/
theorem assembled_actual_ray_pending_source_and_QRH_adapter
    {cs : List Cell}
    (certificate : CompleteCertificate 38358837683 1490000000001 cs)
    (hseries : LogIntegralSeriesIdentity IEANTN.li)
    (hoffset : Middle.LiOffsetIdentity)
    (hpositive : ButhePiBelowLi) (htheta : ButheThetaDeficit)
    (hlower : AxlerPiLower)
    (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    (hCH2 : ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤
      Real.pi / (3 * (10 : ℝ)^12) * t + (113.67 : ℝ) * sqrt t)
    (hDusart : Middle.DusartPowerInput)
    (hpi144 : DudekPlattNumerics.v6.pi_two_sided_144) :
    ∀ x : ℝ, 38358837683 ≤ x →
      primeCounting x ^ 2 < exp 1 * x / log x * primeCounting (x / exp 1) := by
  have hli2 : 0 ≤ IEANTN.li 2 ∧ IEANTN.li 2 ≤ 2 :=
    ⟨(primeCounting_nonneg 2).trans (hpositive 2 (by norm_num)).le, li_two_upper hseries⟩
  have hlog2 : (2 / 3 : ℝ) ≤ log 2 := by linarith [log_two_decimal.1]
  have hDeficit : FiniteMiddle.ButheDeficit19 := by
    intro t ht htU
    exact hbuthe t ⟨ht, htU⟩
  have hBelow : FiniteMiddle.ButheBelow19 := by
    intro t ht htU
    exact (hpositive t ⟨ht, htU⟩).le
  intro x hx
  by_cases hfinite : x < (1490000000001 : ℝ)
  · exact complete_certificate_sound certificate x (by exact_mod_cast hx) hfinite
  have hxFiniteClosed : (1490000000001 : ℝ) ≤ x := le_of_not_gt hfinite
  have hxFinite : (1490000000000 : ℝ) ≤ x := by linarith
  by_cases h19 : x ≤ (10000000000000000000 : ℝ)
  · exact actual_ramanujan_analytic_bridge hseries hoffset hpositive htheta hlower hbuthe
      ⟨hxFinite, h19⟩
  have hx43 : exp (43 : ℝ) ≤ x := exp43_le_1e19.trans (le_of_not_ge h19)
  by_cases h169 : x ≤ exp (169 : ℝ)
  · have hg := FiniteMiddle.actual_middle_gap_from_sources hx43 h169
      hCH2 hDusart hDeficit hBelow hoffset hli2 hlog2
    have hx0 : 0 < x := (exp_pos 43).trans_le hx43
    have hL : (43 : ℝ) ≤ log x := by simpa using log_le_log (exp_pos 43) hx43
    apply (holds_iff_gap_pos x).2
    exact (show (0 : ℝ) < (37 / 200 : ℝ) * x ^ 2 / log x ^ 6 by positivity).trans hg
  · exact QuantitativeTail.holds_of_pi_two_sided_144 hpi144 (le_of_not_ge h169)

#print axioms assembled_actual_ray_pending_source_and_QRH_adapter
end RamanujanPV

namespace RamanujanPV
open Real IEANTN

/-- Adjacency of the actual seven-word rows, including the final next boundary.
This is only an input-format coverage helper; the accepted certificate type remains
CompleteCertificate, exactly as before. -/
inductive RawCellChain : ℕ → ℕ → List RawFactoredCell → Prop where
  | nil (n : ℕ) : RawCellChain n n []
  | cons (r : RawFactoredCell) {stop : ℕ} {rows : List RawFactoredCell}
      (strictNext : r.n < r.next) (rest : RawCellChain r.next stop rows) :
      RawCellChain r.n stop (r :: rows)

theorem RawCellChain.toCellChain {start stop : ℕ} {rows : List RawFactoredCell}
    (chain : RawCellChain start stop rows) (eLo eHi : ℕ) :
    CellChain start stop (rows.map (fun r => r.toCell eLo eHi)) := by
  induction chain with
  | nil n => exact CellChain.nil n
  | @cons r stop rows hn rest ih =>
    change CellChain r.n stop (r.toCell eLo eHi :: rows.map (fun r => r.toCell eLo eHi))
    refine CellChain.cons (r.toCell eLo eHi) ?_
    simpa only [RawFactoredCell.toCell_end r eLo eHi hn] using ih

/-- The exact native seven-word format is transported into the existing final
CompleteCertificate consumer. Every row's A inequality, log enclosure and actual
prime counts is used; the factor A is not an unverified hardcoded oracle. -/
theorem complete_certificate_from_raw {start stop eLo eHi : ℕ} {rows : List RawFactoredCell}
    (chain : RawCellChain start stop rows)
    (checked : ∀ r ∈ rows, r.n < r.next ∧ 0 < r.Lu ∧ r.j * eHi ≤ r.n * 2 ^ 60 ∧
      r.A * r.Lu ≤ r.n * eLo ∧ 2 ^ 20 * r.P ^ 2 < r.A * r.Q)
    (counts : ∀ r ∈ rows, Nat.primeCounting (r.next - 1) = r.P ∧ Nat.primeCounting r.j = r.Q)
    (heLo : (eLo : ℝ) ≤ exp 1 * (2 : ℝ)^60)
    (heHi : exp 1 * (2 : ℝ)^60 ≤ (eHi : ℝ))
    (logs : ∀ r ∈ rows, exp 1 ≤ (r.n : ℝ) ∧ log (r.n : ℝ) * (2 : ℝ)^40 ≤ (r.Lu : ℝ)) :
    CompleteCertificate start stop (rows.map (fun r => r.toCell eLo eHi)) := by
  refine ⟨chain.toCellChain eLo eHi, ?_⟩
  intro c hc
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hn, hLu, hj, hA, hstrict⟩ := checked r hr
  exact ⟨r.toCell_fixedPredicate eLo eHi hn hLu hj hA hstrict,
    r.toCell_counts eLo eHi (counts r hr).1 (counts r hr).2,
    r.toCell_enclosures eLo eHi (logs r hr).1 heLo heHi (logs r hr).2⟩

#print axioms complete_certificate_from_raw
end RamanujanPV
