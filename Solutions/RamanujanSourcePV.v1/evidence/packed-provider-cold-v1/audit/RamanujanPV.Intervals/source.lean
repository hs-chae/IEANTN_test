/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib
import IEANTN.Vocabulary.PrimeCounting

/-! Mathematical consumer for source-verified prime-count and fixed-point cells.
No execution or count certificate is assumed correct merely because it is data.
The source-first checker must supply `CountsCorrect`, `Enclosures`, and `FixedPredicate`. -/
namespace RamanujanPV
open Real IEANTN

/-- The actual inequality, with the IEANTN right-continuous prime count. -/
def Holds (x : ℝ) : Prop :=
  primeCounting x ^ 2 < exp 1 * x / log x * primeCounting (x / exp 1)

noncomputable def gap (x : ℝ) : ℝ :=
  exp 1 * x / log x * primeCounting (x / exp 1) - primeCounting x ^ 2

theorem holds_iff_gap_pos (x : ℝ) : Holds x ↔ 0 < gap x := by
  unfold Holds gap
  constructor <;> intro h <;> linarith

theorem primeCounting_nonneg (x : ℝ) : 0 ≤ primeCounting x := by
  unfold primeCounting
  positivity

theorem primeCounting_mono : Monotone primeCounting := by
  intro x y hxy
  unfold primeCounting
  exact_mod_cast Nat.monotone_primeCounting (Nat.floor_mono hxy)

@[simp] theorem primeCounting_nat (n : ℕ) :
    primeCounting (n : ℝ) = (Nat.primeCounting n : ℝ) := by
  simp [primeCounting]

/-- A half-open integer cell uses the count at m, including every prime at n.
The excluded endpoint m+1 is covered by the following cell. -/
theorem primeCounting_le_of_lt_succ {x : ℝ} {m : ℕ}
    (hx0 : 0 ≤ x) (hx : x < (m : ℝ) + 1) :
    primeCounting x ≤ (Nat.primeCounting m : ℝ) := by
  have hf : ⌊x⌋₊ < m + 1 := (Nat.floor_lt hx0).2 (by exact_mod_cast hx)
  unfold primeCounting
  exact_mod_cast Nat.monotone_primeCounting (Nat.lt_succ_iff.mp hf)

/-- Elementary monotonicity, with the analytic domain made explicit. -/
theorem div_log_mono {a x : ℝ} (ha : exp 1 ≤ a) (hax : a ≤ x) :
    a / log a ≤ x / log x := by
  have ha0 : 0 < a := (exp_pos 1).trans_le ha
  have hx0 : 0 < x := ha0.trans_le hax
  have hla : 0 < log a := by
    have : (1 : ℝ) ≤ log a := by simpa using log_le_log (exp_pos 1) ha
    linarith
  have hlx : 0 < log x := hla.trans_le (log_le_log ha0 hax)
  have h := Real.log_div_self_antitoneOn ha (ha.trans hax) hax
  have hi := one_div_le_one_div_of_le (div_pos hlx hx0) h
  simpa only [one_div_div] using hi

/-- Source-independent real transport for one half-open integer cell. -/
theorem cell_sound {n m j P Q : ℕ} {x : ℝ}
    (hn : exp 1 ≤ (n : ℝ)) (hnx : (n : ℝ) ≤ x) (hxm : x < (m : ℝ) + 1)
    (hP : Nat.primeCounting m = P) (hQ : Nat.primeCounting j = Q)
    (hj : (j : ℝ) * exp 1 ≤ n)
    (hstrict : (P : ℝ)^2 < exp 1 * n / log n * Q) : Holds x := by
  have hn0 : 0 < (n : ℝ) := (exp_pos 1).trans_le hn
  have hx0 : 0 < x := hn0.trans_le hnx
  have hlx : 0 < log x := by
    have : (1 : ℝ) ≤ log x := by
      simpa using log_le_log (exp_pos 1) (hn.trans hnx)
    linarith
  have hupper : primeCounting x ≤ (P : ℝ) := by
    simpa only [hP] using primeCounting_le_of_lt_succ hx0.le hxm
  have hjx : (j : ℝ) ≤ x / exp 1 :=
    (le_div_iff₀ (exp_pos 1)).2 (hj.trans hnx)
  have hlower : (Q : ℝ) ≤ primeCounting (x / exp 1) := by
    simpa only [primeCounting_nat, hQ] using primeCounting_mono hjx
  have hfactor : exp 1 * n / log n ≤ exp 1 * x / log x := by
    have h := mul_le_mul_of_nonneg_left (div_log_mono hn hnx) (exp_pos 1).le
    simpa only [mul_div_assoc] using h
  have hsq : primeCounting x ^ 2 ≤ (P : ℝ) ^ 2 :=
    pow_le_pow_left₀ (primeCounting_nonneg x) hupper 2
  unfold Holds
  calc
    primeCounting x ^ 2 ≤ (P : ℝ)^2 := hsq
    _ < exp 1 * n / log n * Q := hstrict
    _ ≤ exp 1 * x / log x * Q := mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ ≤ exp 1 * x / log x * primeCounting (x / exp 1) :=
      mul_le_mul_of_nonneg_left hlower (by positivity)

/-- Integers actually emitted or read by the C checker. Scale is common to e and log.
Natural-number arithmetic here is mathematical: the source model must separately rule out
machine overflow and prove correspondence with these exact operations. -/
structure Cell where
  n : ℕ
  m : ℕ
  j : ℕ
  P : ℕ
  Q : ℕ
  scale : ℕ
  eLow : ℕ
  eHigh : ℕ
  logHigh : ℕ
  deriving Repr

def Cell.FixedPredicate (c : Cell) : Prop :=
  c.n ≤ c.m ∧ 0 < c.scale ∧ c.j * c.eHigh ≤ c.n * c.scale ∧
    c.P ^ 2 * c.logHigh < c.eLow * c.n * c.Q

def Cell.CountsCorrect (c : Cell) : Prop :=
  Nat.primeCounting c.m = c.P ∧ Nat.primeCounting c.j = c.Q

/-- These are transcendental enclosures, not desired Ramanujan positivity. They too require
source-linked proofs from the chosen e/log implementation. -/
def Cell.Enclosures (c : Cell) : Prop :=
  exp 1 ≤ (c.n : ℝ) ∧ (c.eLow : ℝ) ≤ exp 1 * c.scale ∧
    exp 1 * c.scale ≤ c.eHigh ∧ log (c.n : ℝ) * c.scale ≤ c.logHigh

theorem fixed_cell_sound (c : Cell) (hc : c.FixedPredicate)
    (hcounts : c.CountsCorrect) (henclose : c.Enclosures)
    {x : ℝ} (hnx : (c.n : ℝ) ≤ x) (hxm : x < (c.m : ℝ) + 1) : Holds x := by
  obtain ⟨hnm, hs, hj, hstrict⟩ := hc
  obtain ⟨hn, hel, heu, hl⟩ := henclose
  have hs0 : (0 : ℝ) < c.scale := by exact_mod_cast hs
  have hj' : (c.j : ℝ) * exp 1 ≤ c.n := by
    have hji : (c.j : ℝ) * c.eHigh ≤ c.n * c.scale := by exact_mod_cast hj
    have hje : (c.j : ℝ) * (exp 1 * c.scale) ≤ c.j * c.eHigh :=
      mul_le_mul_of_nonneg_left heu (by positivity)
    nlinarith
  have hlog : 0 < log (c.n : ℝ) := by
    have : (1 : ℝ) ≤ log (c.n : ℝ) := by
      simpa using log_le_log (exp_pos 1) hn
    linarith
  have hraw : (c.P : ℝ)^2 * log c.n < exp 1 * c.n * c.Q := by
    have hsi : (c.P : ℝ)^2 * c.logHigh < c.eLow * c.n * c.Q := by
      exact_mod_cast hstrict
    have hl' := mul_le_mul_of_nonneg_left hl (sq_nonneg (c.P : ℝ))
    have he' := mul_le_mul_of_nonneg_right hel
      (show (0 : ℝ) ≤ (c.n : ℝ) * c.Q by positivity)
    nlinarith
  apply cell_sound hn hnx hxm hcounts.1 hcounts.2 hj'
  simpa only [div_mul_eq_mul_div] using (lt_div_iff₀ hlog).2 hraw

/-- Factored scaled predicate used by the executable generator/checker. In particular
(eScale,logScale,aScale)=(2^60,2^40,2^20) avoids the much larger unfactored
products. The source model still must establish its own uint128 overflow bounds. -/
theorem factored_cell_sound {n m j P Q eScale logScale aScale eLow eHigh logHigh A : ℕ}
    (hlogScale : 0 < logScale) (haScale : 0 < aScale)
    (hscales : eScale = logScale * aScale)
    (hn : exp 1 ≤ (n : ℝ))
    (hP : Nat.primeCounting m = P) (hQ : Nat.primeCounting j = Q)
    (heLow : (eLow : ℝ) ≤ exp 1 * eScale)
    (heHigh : exp 1 * eScale ≤ (eHigh : ℝ))
    (hlogHigh : log (n : ℝ) * logScale ≤ (logHigh : ℝ))
    (hj : j * eHigh ≤ n * eScale)
    (hA : A * logHigh ≤ n * eLow)
    (hstrict : aScale * P ^ 2 < A * Q)
    {x : ℝ} (hnx : (n : ℝ) ≤ x) (hxm : x < (m : ℝ) + 1) : Holds x := by
  have hlS : (0 : ℝ) < logScale := by exact_mod_cast hlogScale
  have haS : (0 : ℝ) < aScale := by exact_mod_cast haScale
  have heS : (0 : ℝ) < eScale := by rw [hscales]; positivity
  have hS : (eScale : ℝ) = (logScale : ℝ) * aScale := by exact_mod_cast hscales
  have hj' : (j : ℝ) * exp 1 ≤ n := by
    have hji : (j : ℝ) * eHigh ≤ n * eScale := by exact_mod_cast hj
    have hje := mul_le_mul_of_nonneg_left heHigh (show (0 : ℝ) ≤ j by positivity)
    apply (mul_le_mul_iff_left₀ heS).mp
    nlinarith
  have hAs : (A : ℝ) * log (n : ℝ) ≤ exp 1 * n * aScale := by
    have hAi : (A : ℝ) * logHigh ≤ n * eLow := by exact_mod_cast hA
    have hAl := mul_le_mul_of_nonneg_left hlogHigh (show (0 : ℝ) ≤ A by positivity)
    have hAe := mul_le_mul_of_nonneg_left heLow (show (0 : ℝ) ≤ n by positivity)
    apply (mul_le_mul_iff_left₀ hlS).mp
    rw [hS] at hAe
    nlinarith
  have hl : 0 < log (n : ℝ) := by
    have : (1 : ℝ) ≤ log (n : ℝ) := by simpa using log_le_log (exp_pos 1) hn
    linarith
  have hs : (aScale : ℝ) * (P : ℝ)^2 < (A : ℝ) * Q := by exact_mod_cast hstrict
  have hs' := mul_lt_mul_of_pos_right hs hl
  have hAs' := mul_le_mul_of_nonneg_right hAs (show (0 : ℝ) ≤ Q by positivity)
  have hraw : (P : ℝ)^2 * log (n : ℝ) < exp 1 * n * Q := by
    apply (mul_lt_mul_iff_right₀ haS).mp
    nlinarith
  apply cell_sound hn hnx hxm hP hQ hj'
  simpa only [div_mul_eq_mul_div] using (lt_div_iff₀ hl).2 hraw

/-- The seven uint64 words actually stored by the native certificate generator.
Global e constants are supplied once, not redundantly trusted per row. -/
structure RawFactoredCell where
  n : ℕ
  next : ℕ
  j : ℕ
  P : ℕ
  Q : ℕ
  Lu : ℕ
  A : ℕ
  deriving Repr

def RawFactoredCell.toCell (r : RawFactoredCell) (eLo eHi : ℕ) : Cell where
  n := r.n
  m := r.next - 1
  j := r.j
  P := r.P
  Q := r.Q
  scale := 2 ^ 60
  eLow := eLo
  eHigh := eHi
  logHigh := r.Lu * 2 ^ 20

/-- The factored A-test implies the ORIGINAL complete-certificate predicate.
Multiplication by Lu is sound because the actual divisor is proved positive. -/
theorem RawFactoredCell.toCell_fixedPredicate (r : RawFactoredCell) (eLo eHi : ℕ)
    (hnext : r.n < r.next) (hLu : 0 < r.Lu)
    (hj : r.j * eHi ≤ r.n * 2 ^ 60)
    (hA : r.A * r.Lu ≤ r.n * eLo)
    (hstrict : 2 ^ 20 * r.P ^ 2 < r.A * r.Q) :
    (r.toCell eLo eHi).FixedPredicate := by
  refine ⟨by change r.n ≤ r.next - 1; omega, by norm_num [toCell], hj, ?_⟩
  change r.P ^ 2 * (r.Lu * 2 ^ 20) < eLo * r.n * r.Q
  have hm := Nat.mul_lt_mul_of_pos_right hstrict hLu
  have ha := Nat.mul_le_mul_right r.Q hA
  nlinarith

theorem RawFactoredCell.toCell_enclosures (r : RawFactoredCell) (eLo eHi : ℕ)
    (hn : exp 1 ≤ (r.n : ℝ))
    (heLo : (eLo : ℝ) ≤ exp 1 * (2 : ℝ)^60)
    (heHi : exp 1 * (2 : ℝ)^60 ≤ (eHi : ℝ))
    (hlog : log (r.n : ℝ) * (2 : ℝ)^40 ≤ (r.Lu : ℝ)) :
    (r.toCell eLo eHi).Enclosures := by
  refine ⟨hn, ?_, ?_, ?_⟩
  · simpa only [toCell, Nat.cast_pow, Nat.cast_ofNat] using heLo
  · simpa only [toCell, Nat.cast_pow, Nat.cast_ofNat] using heHi
  · change log (r.n : ℝ) * ((2 ^ 60 : ℕ) : ℝ) ≤ ((r.Lu * 2 ^ 20 : ℕ) : ℝ)
    have h := mul_le_mul_of_nonneg_right hlog (by norm_num : (0 : ℝ) ≤ 2 ^ 20)
    norm_num [Nat.cast_mul, Nat.cast_pow] at h ⊢
    nlinarith

theorem RawFactoredCell.toCell_counts (r : RawFactoredCell) (eLo eHi : ℕ)
    (hP : Nat.primeCounting (r.next - 1) = r.P) (hQ : Nat.primeCounting r.j = r.Q) :
    (r.toCell eLo eHi).CountsCorrect := ⟨hP, hQ⟩

/-- A strict next boundary becomes exactly the existing half-open cell endpoint. -/
theorem RawFactoredCell.toCell_end (r : RawFactoredCell) (eLo eHi : ℕ)
    (hnext : r.n < r.next) : (r.toCell eLo eHi).m + 1 = r.next := by
  change r.next - 1 + 1 = r.next
  omega

#print axioms RawFactoredCell.toCell_fixedPredicate
#print axioms RawFactoredCell.toCell_enclosures
#print axioms factored_cell_sound
#print axioms fixed_cell_sound
#print axioms cell_sound
end RamanujanPV
