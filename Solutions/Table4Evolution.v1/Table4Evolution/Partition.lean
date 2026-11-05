/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import FKS2Pair.GenericMath

/-!
# The θ → π transport over an arbitrary partition of `[300, 330]`

`FKS2Pair.whole_ray_transport` fixes the 30 unit cells `[300 + j, 301 + j]`. Here the cells are
any list tiling `[300, 330]`, each with its own whole-tail θ allowance `u` valid from `e^{lo}`:

  `Eπ x ≤ (330/300)·e^{-30}·(1.6997e-12 + u₀) + Σ_cells 330·e^{-330}·u·(e^{hi} - e^{lo})/lo² + u₃₃₀ + u₃₃₀/328`

for every `x ≥ e^330` (`whole_ray`). The anchor, point and ray-tail terms are those of
`FKS2Pair.Bsafe`; only the cell sum changes. A cell bound uses `1/log² t ≤ 1/lo²` on
`[e^{lo}, e^{hi}]` and the cell's allowance. With unit cells and `u = U j` this is exactly
`FKS2Pair.cells` (`cellU` after `FKS2Pair.cell_normalization`).

The partition is data. A program generated for a different partition (fewer cells, coarser or
finer ones, non-integer boundaries) is covered by this one theorem without a new proof.
-/

namespace Table4Evolution

open Real IEANTN MeasureTheory Set intervalIntegral FKS2Table4

/-- One cell `[lo, hi]` with a whole-tail θ allowance `u` valid from `e^{lo}`. -/
structure Cell where
  lo : ℝ
  hi : ℝ
  u : ℝ

/-- The cell's allowance is nonnegative and bounds `Eθ` on the whole ray `[e^{lo}, ∞)`. -/
def Cell.Valid (c : Cell) : Prop := 0 ≤ c.u ∧ ∀ t ≥ exp c.lo, Eθ t ≤ c.u

/-- The normalized contribution of one cell to the transport functional. -/
noncomputable def Cell.bound (c : Cell) : ℝ :=
  330 * exp (-330) * c.u * ((exp c.hi - exp c.lo) / c.lo ^ 2)

/-- `cs` tiles `[a, b]`: consecutive cells, the first starting at `a`, the last ending at `b`. -/
def Tiles : ℝ → List Cell → ℝ → Prop
  | a, [], b => a = b
  | a, c :: cs, b => c.lo = a ∧ c.lo ≤ c.hi ∧ Tiles c.hi cs b

theorem Tiles.le : ∀ {a b : ℝ} {cs : List Cell}, Tiles a cs b → a ≤ b
  | a, b, [], h => le_of_eq h
  | a, b, c :: cs, ⟨hlo, hle, hrest⟩ => by
      have := Tiles.le hrest
      rw [← hlo]; linarith

theorem kernel_integral_le {lo hi : ℝ} (hlo : 300 ≤ lo) (hle : lo ≤ hi) :
    (∫ t in exp lo..exp hi, kernel t) ≤ (exp hi - exp lo) / lo ^ 2 := by
  have hab : exp lo ≤ exp hi := exp_le_exp.mpr hle
  have hk := kernel_integrable (by linarith [add_one_le_exp lo]) hab
  have hc : IntervalIntegrable (fun _ : ℝ => 1 / lo ^ 2) volume (exp lo) (exp hi) :=
    intervalIntegrable_const
  have hm := integral_mono_on hab hk hc (fun t ht => by
    have hl : lo ≤ log t := by simpa using log_le_log (exp_pos lo) ht.1
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by linarith) hl 2))
  simpa [intervalIntegral.integral_const, div_eq_mul_inv, mul_comm] using hm

theorem cell_le (c : Cell) (hv : c.Valid) (hlo : 300 ≤ c.lo) (hle : c.lo ≤ c.hi) :
    330 * exp (-330) * |∫ t in exp c.lo..exp c.hi, err t| ≤ c.bound := by
  have hab : exp c.lo ≤ exp c.hi := exp_le_exp.mpr hle
  have h2 : 2 ≤ exp c.lo := by linarith [add_one_le_exp c.lo]
  have hu := uniform_integral_error h2 hab (fun t ht => hv.2 t ht.1)
  have hk := kernel_integral_le hlo hle
  unfold Cell.bound
  calc 330 * exp (-330) * |∫ t in exp c.lo..exp c.hi, err t|
        ≤ 330 * exp (-330) * (c.u * ∫ t in exp c.lo..exp c.hi, kernel t) := by gcongr
    _ ≤ 330 * exp (-330) * (c.u * ((exp c.hi - exp c.lo) / c.lo ^ 2)) := by
        gcongr; exact hv.1
    _ = 330 * exp (-330) * c.u * ((exp c.hi - exp c.lo) / c.lo ^ 2) := by ring

/-- The finite part of the transport, `[e^a, e^b]`, cell by cell. -/
theorem tiles_le : ∀ (cs : List Cell) (a b : ℝ), Tiles a cs b → 300 ≤ a →
    (∀ c ∈ cs, c.Valid) →
    330 * exp (-330) * |∫ t in exp a..exp b, err t| ≤ (cs.map Cell.bound).sum
  | [], a, b, hT, _, _ => by
      have hab : a = b := hT
      subst hab
      simp
  | c :: cs, a, b, hT, ha, hv => by
      obtain ⟨hlo, hle, hrest⟩ := hT
      have hca : 300 ≤ c.lo := by rw [hlo]; exact ha
      have hcell := cell_le c (hv c (by simp)) hca hle
      have hih := tiles_le cs c.hi b hrest (by linarith) (fun d hd => hv d (by simp [hd]))
      have hhb : c.hi ≤ b := Tiles.le hrest
      have h1 : exp a ≤ exp c.hi := exp_le_exp.mpr (by rw [← hlo]; exact hle)
      have h2 : exp c.hi ≤ exp b := exp_le_exp.mpr hhb
      have ha2 : 1 < exp a := by linarith [add_one_le_exp a]
      have hsplit := integral_add_adjacent_intervals
        (FKS2Sol.intervalIntegrable_sub_div ha2 h1)
        (FKS2Sol.intervalIntegrable_sub_div (by linarith) h2)
      have htri : |∫ t in exp a..exp b, err t| ≤
          |∫ t in exp a..exp c.hi, err t| + |∫ t in exp c.hi..exp b, err t| := by
        change |∫ t in exp a..exp b, (Chebyshev.theta t - t) / (t * (log t) ^ 2)| ≤ _
        rw [← hsplit]
        exact abs_add_le _ _
      rw [hlo] at hcell
      simp only [List.map_cons, List.sum_cons]
      have hpos : (0 : ℝ) ≤ 330 * exp (-330) := by positivity
      have := mul_le_mul_of_nonneg_left htri hpos
      linarith

/-- The allowance of a partition `cs` with anchor allowance `u0` and ray allowance `u330`. -/
noncomputable def allowance (cs : List Cell) (u0 u330 : ℝ) : ℝ :=
  (330 / 300) * exp (-30) * (1.6997e-12 + u0) + (cs.map Cell.bound).sum + u330 + u330 / 328

/-- **Whole-ray transport over a partition.** -/
theorem whole_ray (cs : List Cell) (hT : Tiles 300 cs 330) (hv : ∀ c ∈ cs, c.Valid)
    {u0 u330 : ℝ} (h0 : Eθ (exp 300) ≤ u0) (hu330 : 0 ≤ u330)
    (h330 : ∀ t ≥ exp 330, Eθ t ≤ u330) (hOld : Eπ (exp 300) ≤ 1.6997e-12) :
    ∀ x ≥ exp 330, Eπ x ≤ allowance cs u0 u330 := by
  intro x hx
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have h330' : 2 ≤ exp (330 : ℝ) := by linarith [add_one_le_exp (330 : ℝ)]
  have h300 : 2 ≤ exp (300 : ℝ) := by linarith [add_one_le_exp (300 : ℝ)]
  have hab : exp (300 : ℝ) ≤ exp 330 := exp_le_exp.mpr (by norm_num)
  have hm : 0 ≤ log x / x := by
    have := log_le_log (exp_pos (330 : ℝ)) hx; rw [log_exp] at this; positivity
  have hp := FKS2Sol.Epi_le h300 (hab.trans hx)
  have hsplit := integral_add_adjacent_intervals
    (FKS2Sol.intervalIntegrable_sub_div (by linarith) hab)
    (FKS2Sol.intervalIntegrable_sub_div (by linarith) hx)
  have htri : |∫ t in exp 300..x, err t| ≤
      |∫ t in exp 300..exp 330, err t| + |∫ t in exp 330..x, err t| := by
    change |∫ t in exp 300..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2)| ≤ _
    rw [← hsplit]
    exact abs_add_le _ _
  have hA := FKS2Pair.bounded_anchor h0 hOld
  have hmono := log_div_antitone (by norm_num : (1 : ℝ) ≤ 330) hx
  have hanchor : log x / x * |primeCounting (exp 300) - Li (exp 300) -
      (Chebyshev.theta (exp 300) - exp 300) / log (exp 300)| ≤
      (330 / 300) * exp (-30) * (1.6997e-12 + u0) := by
    rw [log_exp]
    calc
      _ ≤ (330 * exp (-330)) * (exp 300 / 300 * (1.6997e-12 + u0)) :=
        mul_le_mul hmono hA (abs_nonneg _) (by positivity)
      _ = _ := by
        have he : exp (-330) * exp 300 = exp (-30 : ℝ) := by rw [← exp_add]; norm_num
        calc
          _ = (330 / 300) * (exp (-330) * exp 300) * (1.6997e-12 + u0) := by ring
          _ = _ := by rw [he]
  have hfinite := (mul_le_mul_of_nonneg_right hmono (abs_nonneg
    (∫ t in exp 300..exp 330, err t))).trans (tiles_le cs 300 330 hT le_rfl hv)
  have ht := uniform_integral_error h330' hx (fun t ht => h330 t ht.1)
  have htail : log x / x * |∫ t in exp 330..x, err t| ≤ u330 / 328 := by
    have h := mul_le_mul_of_nonneg_left ht hm
    have hnorm := mul_le_mul_of_nonneg_left (normalized_kernel_tail hx) hu330
    nlinarith [h, hnorm]
  have hpoint := h330 x hx
  change Eπ x ≤ log x / x * |primeCounting (exp 300) - Li (exp 300) -
      (Chebyshev.theta (exp 300) - exp 300) / log (exp 300)| + Eθ x +
      log x / x * |∫ t in exp 300..x, err t| at hp
  have hmul := mul_le_mul_of_nonneg_left htri hm
  unfold allowance
  linarith

end Table4Evolution
