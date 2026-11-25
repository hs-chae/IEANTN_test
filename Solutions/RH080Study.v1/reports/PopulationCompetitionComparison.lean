import Mathlib.Tactic

/-! Exact comparison of three stated scalar formulas. No prime-counting theorem,
Fourier reduction, program verification, onset transfer or optimality is asserted. -/
namespace RH080.PopulationCompetition
noncomputable section

def q : ℝ := 82325773717 / 98718416336
def G (α : ℝ) : ℝ := q * (1 + 2 * α)
def P₁ (α : ℝ) : ℝ := 851127043 / 1000000000 + (1505827 / 1000000) * α
def P₂ (α : ℝ) : ℝ := 85124642 / 100000000 + (1505237 / 1000000) * α
def P (α : ℝ) : ℝ := min (P₁ α) (P₂ α)
def Oline (α : ℝ) : ℝ := 163827 / 160000 + (9 / 8) * α
def O (α : ℝ) : ℝ := max (103 / 100) (Oline α)
def envelope (α : ℝ) : ℝ := min (G α) (min (P α) (O α))

def a : ℝ := 106008754293910903 / 999918169875633000
def c : ℝ := 119377 / 590000
def b : ℝ := 17267233 / 38023700
def d : ℝ := 187538637397367 / 535933290560000

theorem crossing_order : 0 < a ∧ a < c ∧ c < d ∧ d < b ∧ b < 2 := by
  norm_num [a, c, d, b]

theorem G_le_P₁ (α : ℝ) : G α ≤ P₁ α ↔ α ≤ a := by
  dsimp [G, P₁, q, a]
  norm_num
  constructor <;> intro h <;> nlinarith

theorem P₁_le_P₂ (α : ℝ) : P₁ α ≤ P₂ α ↔ α ≤ c := by
  dsimp [P₁, P₂, c]
  norm_num
  constructor <;> intro h <;> nlinarith

theorem P₂_le_Oline (α : ℝ) : P₂ α ≤ Oline α ↔ α ≤ b := by
  dsimp [P₂, Oline, b]
  norm_num
  constructor <;> intro h <;> nlinarith

theorem G_le_Oline (α : ℝ) : G α ≤ Oline α ↔ α ≤ d := by
  dsimp [G, Oline, q, d]
  norm_num
  constructor <;> intro h <;> nlinarith

theorem P₁_le_G (α : ℝ) (h : a ≤ α) : P₁ α ≤ G α := by
  dsimp [G, P₁, q, a] at *
  norm_num at *
  linarith

theorem P₂_le_P₁ (α : ℝ) (h : c ≤ α) : P₂ α ≤ P₁ α := by
  dsimp [P₁, P₂, c] at *
  norm_num at *
  linarith

theorem Oline_le_P₂ (α : ℝ) (h : b ≤ α) : Oline α ≤ P₂ α := by
  dsimp [P₂, Oline, b] at *
  norm_num at *
  linarith

theorem Oline_le_G (α : ℝ) (h : d ≤ α) : Oline α ≤ G α := by
  dsimp [G, Oline, q, d] at *
  norm_num at *
  linarith

theorem O_eq_line (α : ℝ) (h : b ≤ α) : O α = Oline α := by
  apply max_eq_right
  dsimp [Oline, b] at *
  norm_num at *
  linarith

theorem envelope_G (α : ℝ) (h : α ≤ a) : envelope α = G α := by
  have gp : G α ≤ P₁ α := (G_le_P₁ α).2 h
  have p12 : P₁ α ≤ P₂ α := (P₁_le_P₂ α).2 (h.trans (le_of_lt crossing_order.2.1))
  have go : G α ≤ Oline α := (G_le_Oline α).2
    (h.trans (le_of_lt (crossing_order.2.1.trans crossing_order.2.2.1)))
  exact min_eq_left (le_min (le_min gp (gp.trans p12)) (go.trans (le_max_right _ _)))

theorem envelope_P₁ (α : ℝ) (ha : a ≤ α) (hc : α ≤ c) : envelope α = P₁ α := by
  have pg := P₁_le_G α ha
  have p12 := (P₁_le_P₂ α).2 hc
  have p2o := (P₂_le_Oline α).2
    (hc.trans (le_of_lt (crossing_order.2.2.1.trans crossing_order.2.2.2.1)))
  have po : P₁ α ≤ O α := (p12.trans p2o).trans (le_max_right _ _)
  change min (G α) (min (min (P₁ α) (P₂ α)) (O α)) = P₁ α
  rw [min_eq_left p12, min_eq_left po, min_eq_right pg]

theorem envelope_P₂ (α : ℝ) (hc : c ≤ α) (hb : α ≤ b) : envelope α = P₂ α := by
  have p21 := P₂_le_P₁ α hc
  have p1g := P₁_le_G α ((le_of_lt crossing_order.2.1).trans hc)
  have p2o : P₂ α ≤ O α := ((P₂_le_Oline α).2 hb).trans (le_max_right _ _)
  change min (G α) (min (min (P₁ α) (P₂ α)) (O α)) = P₂ α
  rw [min_eq_right p21, min_eq_left p2o, min_eq_right (p21.trans p1g)]

theorem envelope_O (α : ℝ) (hb : b ≤ α) : envelope α = O α := by
  have hd : d ≤ α := (le_of_lt crossing_order.2.2.2.1).trans hb
  have hc : c ≤ α := (le_of_lt (crossing_order.2.2.1.trans crossing_order.2.2.2.1)).trans hb
  have op2 := Oline_le_P₂ α hb
  have op1 := op2.trans (P₂_le_P₁ α hc)
  have og := Oline_le_G α hd
  change min (G α) (min (min (P₁ α) (P₂ α)) (O α)) = O α
  rw [O_eq_line α hb, min_eq_right (le_min op1 op2), min_eq_right og]

theorem paper_strictly_smaller_at_old_crossing :
    P d < G d ∧ G d = O d := by
  norm_num [P, P₁, P₂, G, O, Oline, q, d]

theorem continuous_envelope : Continuous envelope := by
  unfold envelope G P P₁ P₂ O Oline
  fun_prop

#print axioms crossing_order
#print axioms G_le_P₁
#print axioms P₁_le_P₂
#print axioms P₂_le_Oline
#print axioms G_le_Oline
#print axioms envelope_G
#print axioms envelope_P₁
#print axioms envelope_P₂
#print axioms envelope_O
#print axioms paper_strictly_smaller_at_old_crossing
#print axioms continuous_envelope
end
end RH080.PopulationCompetition
