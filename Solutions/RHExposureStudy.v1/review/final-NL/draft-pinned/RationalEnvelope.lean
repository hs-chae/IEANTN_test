import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Actual executable rational program, with kernel-checked real soundness.
The caller supplies the radii and right scaled-error bounds. This file
does not claim any external transcendental or zeta error bound. -/
namespace RHEnvelope

def Poly (cs : List ℚ) (z : ℝ) (k : ℕ) : ℝ :=
  match cs with
  | [] => 0
  | c :: ds => (c : ℝ) * z^k + Poly ds z (k+1)

def lower (cs : List ℚ) (lo hi : ℚ) (k : ℕ) : ℚ :=
  match cs with
  | [] => 0
  | c :: ds => c * (if 0 ≤ c then lo else hi)^k + lower ds lo hi (k+1)

theorem lower_correct (cs : List ℚ) (lo hi : ℚ) (z : ℝ) (k : ℕ)
    (h₀ : 0 ≤ (lo : ℝ)) (hl : (lo : ℝ) ≤ z) (hu : z ≤ (hi : ℝ)) :
    (lower cs lo hi k : ℝ) ≤ Poly cs z k := by
  induction cs generalizing k with
  | nil => simp [lower, Poly]
  | cons c ds ih =>
    simp only [lower, Poly, Rat.cast_add, Rat.cast_mul, Rat.cast_pow]
    refine add_le_add ?_ (ih (k+1))
    by_cases hc : 0 ≤ c
    · simp only [if_pos hc]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h₀ hl _) (by exact_mod_cast hc)
    · simp only [if_neg hc]
      exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (h₀.trans hl) hu _)
        (by exact_mod_cast (le_of_not_ge hc))

structure Cell where
  lo : ℚ
  hi : ℚ
  penalty : ℚ
  margin : ℚ
  deriving Repr

def check (cs : List ℚ) (c : Cell) : Bool :=
  decide (0 ≤ c.lo ∧ c.margin ≤ lower cs c.lo c.hi 0 - c.penalty)

theorem check_correct {cs c} (h : check cs c = true)
    {z error : ℝ} (hz₀ : (c.lo : ℝ) ≤ z) (hz₁ : z ≤ c.hi)
    (he : error ≤ c.penalty) :
    (c.margin : ℝ) ≤ Poly cs z 0 - error := by
  have hp := of_decide_eq_true h
  have hh : (c.margin : ℝ) ≤ (lower cs c.lo c.hi 0 : ℝ) - c.penalty := by
    exact_mod_cast hp.2
  exact hh.trans (sub_le_sub (lower_correct cs c.lo c.hi z 0 (by exact_mod_cast hp.1)
    hz₀ hz₁) he)

def program (cs : List ℚ) (table : List Cell) : Bool :=
  table.all (fun c => check cs c)

-- Operational semantics for running this straight-line cell checker on a list.
inductive Run (cs : List ℚ) : List Cell → Bool → Prop
  | stop : Run cs [] true
  | reject {c vs} : check cs c = false → Run cs (c :: vs) false
  | next {c vs out} : check cs c = true → Run cs vs out → Run cs (c :: vs) out

theorem execution (cs table) : Run cs table (program cs table) := by
  induction table with
  | nil => exact .stop
  | cons c vs ih =>
    unfold program
    simp only [List.all_cons]
    cases h : check cs c with
    | false =>
      simp only [Bool.false_and]
      exact .reject h
    | true =>
      simp only [Bool.true_and]
      exact .next h ih

theorem sound_run {cs table out} (h : Run cs table out) (ho : out = true) {c : Cell} (hc : c ∈ table)
    {z error : ℝ} (hz₀ : (c.lo : ℝ) ≤ z) (hz₁ : z ≤ c.hi)
    (he : error ≤ c.penalty) :
    (c.margin : ℝ) ≤ Poly cs z 0 - error := by
  induction h with
  | stop => simp at hc
  | reject => cases ho
  | next hcheck ht ih =>
    rcases List.mem_cons.mp hc with rfl | htail
    · exact check_correct hcheck hz₀ hz₁ he
    · exact ih ho htail

theorem program_correct {cs table} (h : program cs table = true) {c : Cell}
    (hc : c ∈ table) {z error : ℝ} (hz₀ : (c.lo : ℝ) ≤ z) (hz₁ : z ≤ c.hi)
    (he : error ≤ c.penalty) :
    (c.margin : ℝ) ≤ Poly cs z 0 - error := by
  have ex := execution cs table
  rw [h] at ex
  exact sound_run ex rfl hc hz₀ hz₁ he

#print axioms RHEnvelope.program_correct
end RHEnvelope
