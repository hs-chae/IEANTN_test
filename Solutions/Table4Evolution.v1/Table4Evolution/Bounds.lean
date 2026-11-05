/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.Partition
import FKS2Table4.Certificates

/-!
# Rational upper bounds for the cells of a partition

Every profile used here has, on a cell `[lo, hi]`, an allowance of the form `u = m·e^{-s·lo}`:

* QRH, `Q(L) = L²/283·e^{-L/8}`: `s = 1/8`, `m = lo²/283`;
* a power bound `Eθ ≤ K·x^{-1/8}` (for instance Agent A's): `s = 1/8`, `m = K`;
* a step profile (the QRH-free Table 3 allowances): `s = 0`, `m` the step value.

Then `Cell.bound = (330·m/lo²)·(e^{hi - s·lo - 330} - e^{(1-s)·lo - 330})`, and the two exponentials
are enclosed by `FKS2Scalar.expCheck` at a quarter of the exponent, as in `FKS2Table4`. `cellsOK`
checks a whole partition at once: the exponential certificates, `300 ≤ lo ≤ hi`, and
`2^k·(upper bound) ≤ x` for the program's literal `x`. `cellsOK_sound` turns it into the tiling and
the bound `Σ cells ≤ 2^{-k}·Σ x` that the program bridge needs.
-/

namespace Table4Evolution

open Real IEANTN FKS2Scalar

theorem exp4_le {y : ℚ} (h : expCheck y (expLo y) (expHi y) = true) :
    exp (4 * (y : ℝ)) ≤ (((expHi y) ^ 4 : ℚ) : ℝ) := by
  have he := (expCheck_sound h).2
  rw [show (4 : ℝ) * y = ((4 : ℕ) : ℝ) * y by norm_num, Real.exp_nat_mul]
  push_cast
  exact pow_le_pow_left₀ (exp_nonneg _) he 4

theorem le_exp4 {y : ℚ} (h : expCheck y (expLo y) (expHi y) = true) (h0 : 0 ≤ expLo y) :
    (((expLo y) ^ 4 : ℚ) : ℝ) ≤ exp (4 * (y : ℝ)) := by
  have he := (expCheck_sound h).1
  rw [show (4 : ℝ) * y = ((4 : ℕ) : ℝ) * y by norm_num, Real.exp_nat_mul]
  push_cast
  exact pow_le_pow_left₀ (by exact_mod_cast h0) he 4

/-- The cell `[lo, hi]` of a profile with allowance `m·e^{-s·lo}`. -/
noncomputable def expCell (s m lo hi : ℚ) : Cell := ⟨lo, hi, (m : ℝ) * exp (-((s : ℝ) * lo))⟩

def cellA (s lo hi : ℚ) : ℚ := (hi - s * lo - 330) / 4
def cellB (s lo : ℚ) : ℚ := ((1 - s) * lo - 330) / 4

/-- The rational upper bound of `(expCell s m lo hi).bound`. -/
def cellHi (s m lo hi : ℚ) : ℚ :=
  (330 * m / lo ^ 2) * ((expHi (cellA s lo hi)) ^ 4 - (expLo (cellB s lo)) ^ 4)

/-- One cell's certificate against the program literal `x` at scale `2^{-k}`. -/
def cellOK (s : ℚ) (k : ℕ) (m lo hi x : ℚ) : Bool :=
  expCheck (cellA s lo hi) (expLo (cellA s lo hi)) (expHi (cellA s lo hi)) &&
  expCheck (cellB s lo) (expLo (cellB s lo)) (expHi (cellB s lo)) &&
  decide (0 ≤ expLo (cellB s lo)) && decide (0 ≤ m) && decide (300 ≤ lo) && decide (lo ≤ hi) &&
  decide (2 ^ k * cellHi s m lo hi ≤ x)

theorem expCell_bound_eq (s m lo hi : ℚ) (hlo : (0 : ℝ) < lo) :
    (expCell s m lo hi).bound =
      (330 * (m : ℝ) / (lo : ℝ) ^ 2) * (exp (4 * ((cellA s lo hi : ℚ) : ℝ)) -
        exp (4 * ((cellB s lo : ℚ) : ℝ))) := by
  unfold Cell.bound expCell cellA cellB
  simp only
  push_cast
  have e1 : exp (-330) * exp (-((s : ℝ) * lo)) * exp (hi : ℝ) =
      exp (4 * (((hi : ℝ) - s * lo - 330) / 4)) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  have e2 : exp (-330) * exp (-((s : ℝ) * lo)) * exp (lo : ℝ) =
      exp (4 * (((1 - (s : ℝ)) * lo - 330) / 4)) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  rw [← e1, ← e2]
  field_simp

theorem cellOK_bound {s : ℚ} {k : ℕ} {m lo hi x : ℚ} (h : cellOK s k m lo hi x = true) :
    (expCell s m lo hi).bound ≤ (((1 / 2 ^ k : ℚ) * x : ℚ) : ℝ) := by
  simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hA, hB⟩, hB0⟩, hm⟩, h300⟩, hle⟩, hx⟩ := h
  have hlo : (0 : ℝ) < lo := by
    have : (300 : ℚ) ≤ lo := h300
    have : (0 : ℚ) < lo := by linarith
    exact_mod_cast this
  rw [expCell_bound_eq s m lo hi hlo]
  have hup := exp4_le hA
  have hdn := le_exp4 hB hB0
  have hcoef : (0 : ℝ) ≤ 330 * (m : ℝ) / (lo : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ m := by exact_mod_cast hm
    positivity
  have hstep : (330 * (m : ℝ) / (lo : ℝ) ^ 2) * (exp (4 * ((cellA s lo hi : ℚ) : ℝ)) -
      exp (4 * ((cellB s lo : ℚ) : ℝ))) ≤ ((cellHi s m lo hi : ℚ) : ℝ) := by
    unfold cellHi
    push_cast
    apply mul_le_mul_of_nonneg_left _ hcoef
    push_cast at hup hdn
    linarith
  have hxq : cellHi s m lo hi ≤ (1 / 2 ^ k : ℚ) * x := by
    have h2 : (0 : ℚ) < 2 ^ k := by positivity
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h2]
    linarith [hx]
  calc _ ≤ ((cellHi s m lo hi : ℚ) : ℝ) := hstep
    _ ≤ _ := by exact_mod_cast hxq

/-- The cells of the partition with boundaries `bs`, allowance `mOf lo·e^{-s·lo}` on `[lo, hi]`. -/
noncomputable def cellsOf (s : ℚ) (mOf : ℚ → ℚ) : List ℚ → List Cell
  | lo :: hi :: bs => expCell s (mOf lo) lo hi :: cellsOf s mOf (hi :: bs)
  | _ => []

/-- The whole partition's certificate: one `cellOK` per cell, literals in order. -/
def cellsOK (s : ℚ) (k : ℕ) (mOf : ℚ → ℚ) : List ℚ → List ℚ → Bool
  | lo :: hi :: bs, x :: xs => cellOK s k (mOf lo) lo hi x && cellsOK s k mOf (hi :: bs) xs
  | [_], [] => true
  | _, _ => false

theorem cellsOK_sound (s : ℚ) (k : ℕ) (mOf : ℚ → ℚ) :
    ∀ (b : ℚ) (bs xs : List ℚ), cellsOK s k mOf (b :: bs) xs = true →
      Tiles (b : ℝ) (cellsOf s mOf (b :: bs)) (((b :: bs).getLast (List.cons_ne_nil _ _) : ℚ) : ℝ) ∧
      ((cellsOf s mOf (b :: bs)).map Cell.bound).sum ≤ (((1 / 2 ^ k : ℚ) * xs.sum : ℚ) : ℝ)
  | b, [], xs, h => by
      cases xs with
      | nil => simp [cellsOf, Tiles]
      | cons x xs => simp [cellsOK] at h
  | b, hi :: bs, [], h => by simp [cellsOK] at h
  | b, hi :: bs, x :: xs, h => by
      simp only [cellsOK, Bool.and_eq_true] at h
      obtain ⟨hc, hrest⟩ := h
      obtain ⟨hT, hS⟩ := cellsOK_sound s k mOf hi bs xs hrest
      have hb := cellOK_bound hc
      have hle : b ≤ hi := by
        simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.1.2
      refine ⟨⟨rfl, by simp only [expCell]; exact_mod_cast hle, ?_⟩, ?_⟩
      · simpa [expCell, List.getLast_cons] using hT
      · simp only [cellsOf, List.map_cons, List.sum_cons]
        push_cast at hb hS ⊢
        linarith

/-- Validity of every cell from a profile statement on rational left endpoints `≥ 300`. -/
theorem cellsOf_valid (s : ℚ) (mOf : ℚ → ℚ)
    (hprof : ∀ lo : ℚ, 300 ≤ lo → 0 ≤ mOf lo ∧
      ∀ t ≥ exp (lo : ℝ), Eθ t ≤ (mOf lo : ℝ) * exp (-((s : ℝ) * lo))) (k : ℕ) :
    ∀ (b : ℚ) (bs xs : List ℚ), cellsOK s k mOf (b :: bs) xs = true →
      ∀ c ∈ cellsOf s mOf (b :: bs), c.Valid
  | b, [], xs, _ => by simp [cellsOf]
  | b, hi :: bs, [], h => by simp [cellsOK] at h
  | b, hi :: bs, x :: xs, h => by
      simp only [cellsOK, Bool.and_eq_true] at h
      obtain ⟨hc, hrest⟩ := h
      have h300 : (300 : ℚ) ≤ b := by
        simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.1.1.2
      intro c hcmem
      simp only [cellsOf, List.mem_cons] at hcmem
      rcases hcmem with rfl | hmem
      · obtain ⟨hm, hθ⟩ := hprof b h300
        have hm' : (0 : ℝ) ≤ mOf b := by exact_mod_cast hm
        exact ⟨show (0 : ℝ) ≤ (mOf b : ℝ) * exp (-((s : ℝ) * b)) from
          mul_nonneg hm' (exp_pos _).le, hθ⟩
      · exact cellsOf_valid s mOf hprof k hi bs xs hrest c hmem

end Table4Evolution

namespace Table4Evolution

open Real IEANTN FKS2Scalar

/-! ### The anchor, point and tail constants of a profile `m·e^{-s·L}` -/

def y0 (s : ℚ) : ℚ := -(s * 300) / 4
def y330 (s : ℚ) : ℚ := -(s * 330) / 4

/-- An upper bound of `e^{4y}`: exactly `1` at `y = 0` (a constant profile), else `expHi y ^ 4`. -/
def expUp (y : ℚ) : ℚ := if y = 0 then 1 else expHi y ^ 4

/-- The certificate behind `expUp`. -/
def expUpOK (y : ℚ) : Bool := decide (y = 0) || expCheck y (expLo y) (expHi y)

theorem exp_le_expUp {y : ℚ} (h : expUpOK y = true) : exp (4 * (y : ℝ)) ≤ (expUp y : ℝ) := by
  unfold expUpOK at h
  unfold expUp
  by_cases hy : y = 0
  · simp [hy]
  · simp only [hy, decide_false, Bool.false_or] at h
    simp only [hy, if_false]
    exact exp4_le h

def anchorHi (s m0 : ℚ) : ℚ := (330 / 300) * expHi (-15) ^ 2 * (1.6997e-12 + m0 * expUp (y0 s))
def pointHi (s m330 : ℚ) : ℚ := m330 * expUp (y330 s)

/-- The three constants of a program against the profile's anchor, point and tail. -/
def constOK (s m0 m330 a p t : ℚ) : Bool :=
  expUpOK (y0 s) && expUpOK (y330 s) &&
  expCheck (-15) (expLo (-15)) (expHi (-15)) &&
  decide (0 ≤ m0) && decide (0 ≤ m330) &&
  decide (anchorHi s m0 ≤ a) && decide (pointHi s m330 ≤ p) && decide (pointHi s m330 / 328 ≤ t)

theorem constOK_sound {s m0 m330 a p t : ℚ} (h : constOK s m0 m330 a p t = true) :
    (330 / 300) * exp (-30) * (1.6997e-12 + (m0 : ℝ) * exp (-((s : ℝ) * 300))) +
      (m330 : ℝ) * exp (-((s : ℝ) * 330)) + (m330 : ℝ) * exp (-((s : ℝ) * 330)) / 328 ≤
      (a : ℝ) + p + t := by
  simp only [constOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h330⟩, h15⟩, hm0⟩, hm330⟩, ha⟩, hp⟩, ht⟩ := h
  have hm0' : (0 : ℝ) ≤ m0 := by exact_mod_cast hm0
  have hm330' : (0 : ℝ) ≤ m330 := by exact_mod_cast hm330
  have e0 : exp (-((s : ℝ) * 300)) ≤ ((expUp (y0 s) : ℚ) : ℝ) := by
    have := exp_le_expUp h0
    have e : (4 : ℝ) * ((y0 s : ℚ) : ℝ) = -((s : ℝ) * 300) := by unfold y0; push_cast; ring
    rwa [e] at this
  have e330 : exp (-((s : ℝ) * 330)) ≤ ((expUp (y330 s) : ℚ) : ℝ) := by
    have := exp_le_expUp h330
    have e : (4 : ℝ) * ((y330 s : ℚ) : ℝ) = -((s : ℝ) * 330) := by unfold y330; push_cast; ring
    rwa [e] at this
  have e30 : exp (-30 : ℝ) ≤ ((expHi (-15) ^ 2 : ℚ) : ℝ) := by
    have h := FKS2Table4.exp_pow_upper (n := 2) h15
    norm_num at h ⊢; exact h
  have hu0 : (m0 : ℝ) * exp (-((s : ℝ) * 300)) ≤ (m0 : ℝ) * ((expUp (y0 s) : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left e0 hm0'
  have hpt : (m330 : ℝ) * exp (-((s : ℝ) * 330)) ≤ (pointHi s m330 : ℝ) := by
    unfold pointHi; push_cast
    push_cast at e330
    exact mul_le_mul_of_nonneg_left e330 hm330'
  have hanc : (330 / 300) * exp (-30) * (1.6997e-12 + (m0 : ℝ) * exp (-((s : ℝ) * 300))) ≤
      (anchorHi s m0 : ℝ) := by
    unfold anchorHi
    push_cast
    push_cast at e30 hu0
    have hnn : (0 : ℝ) ≤ 1.6997e-12 + (m0 : ℝ) * exp (-((s : ℝ) * 300)) := by positivity
    calc (330 / 300) * exp (-30) * (1.6997e-12 + (m0 : ℝ) * exp (-((s : ℝ) * 300)))
        ≤ (330 / 300) * (expHi (-15) : ℝ) ^ 2 * (1.6997e-12 + (m0 : ℝ) * exp (-((s : ℝ) * 300))) := by
          gcongr
      _ ≤ (330 / 300) * (expHi (-15) : ℝ) ^ 2 * (1.6997e-12 + (m0 : ℝ) * (expUp (y0 s) : ℝ)) := by
          gcongr
  have haR : (anchorHi s m0 : ℝ) ≤ a := by exact_mod_cast ha
  have hpR : (pointHi s m330 : ℝ) ≤ p := by exact_mod_cast hp
  have htR : ((pointHi s m330 / 328 : ℚ) : ℝ) ≤ t := by exact_mod_cast ht
  push_cast at htR
  have : (m330 : ℝ) * exp (-((s : ℝ) * 330)) / 328 ≤ (pointHi s m330 : ℝ) / 328 := by
    linarith [div_le_div_of_nonneg_right hpt (by norm_num : (0 : ℝ) ≤ 328)]
  linarith

end Table4Evolution
