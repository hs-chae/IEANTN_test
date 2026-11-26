/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RH080Next.FFT.Limbs

def value (B n : ℕ) (d : ℕ → ℕ) : ℤ :=
  ∑ j ∈ Finset.range n, (d j:ℤ)*(B:ℤ)^j

theorem value_succ (B n : ℕ) (d : ℕ → ℕ) :
    value B (n+1) d=value B n d+(d n:ℤ)*(B:ℤ)^n := by
  exact Finset.sum_range_succ _ _

theorem value_update (B n k v : ℕ) (d : ℕ → ℕ) (hk : k < n) :
    value B n (Function.update d k v)=value B n d+((v:ℤ)-(d k:ℤ))*(B:ℤ)^k := by
  have he : (fun j => ((Function.update d k v j:ℕ):ℤ)*(B:ℤ)^j)=
      Function.update (fun j => (d j:ℤ)*(B:ℤ)^j) k ((v:ℤ)*(B:ℤ)^k) := by
    funext j
    by_cases h : j=k <;> simp [h]
  unfold value
  rw [he,Finset.sum_update_of_mem (Finset.mem_range.mpr hk)]
  have ho := Finset.sum_update_of_mem (Finset.mem_range.mpr hk)
    (fun j => (d j:ℤ)*(B:ℤ)^j) ((d k:ℤ)*(B:ℤ)^k)
  simp only [Function.update_eq_self] at ho
  linarith

/-- The actual source's inner row recurrence, in mathematical digit form.
The C refinement must separately establish its loads, stores and word bounds. -/
def row (B offset a : ℕ) (b initial : ℕ → ℕ) : ℕ → ((ℕ → ℕ) × ℕ)
  | 0 => (initial,0)
  | j+1 =>
    let r := row B offset a b initial j
    let t := r.1 (offset+j)+a*b j+r.2
    (Function.update r.1 (offset+j) (t%B),t/B)

theorem row_untouched (B offset a : ℕ) (b initial : ℕ → ℕ) (j k : ℕ)
    (hk : k < offset ∨ offset+j ≤ k) :
    (row B offset a b initial j).1 k=initial k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hne : k≠offset+j := by omega
    simp only [row,Function.update_of_ne hne]
    exact ih (by omega)

/-- Global numerical invariant of an entire row, including the carry.
This does not assume the desired product as a certificate or execution fact. -/
theorem row_value (B offset a : ℕ) (b initial : ℕ → ℕ) (n j : ℕ)
    (hj : offset+j ≤ n) :
    value B n (row B offset a b initial j).1+
      ((row B offset a b initial j).2:ℤ)*(B:ℤ)^(offset+j)=
        value B n initial+(a:ℤ)*value B j b*(B:ℤ)^offset := by
  induction j with
  | zero => simp [row,value]
  | succ j ih =>
    have ih' := ih (by omega)
    let r := row B offset a b initial j
    let t := r.1 (offset+j)+a*b j+r.2
    have hd : ((t%B:ℕ):ℤ)+(B:ℤ)*((t/B:ℕ):ℤ)=
        (r.1 (offset+j):ℤ)+(a:ℤ)*(b j:ℤ)+(r.2:ℤ) := by
      have hh := Nat.mod_add_div t B
      dsimp [t] at hh ⊢
      exact_mod_cast hh
    have hp : (B:ℤ)^(offset+(j+1))=(B:ℤ)^(offset+j)*(B:ℤ) := by
      rw [show offset+(j+1)=offset+j+1 by omega,pow_succ]
    have hp' : (B:ℤ)^j*(B:ℤ)^offset=(B:ℤ)^(offset+j) := by
      rw [←pow_add,Nat.add_comm]
    change value B n (Function.update r.1 (offset+j) (t%B))+
      ((t/B:ℕ):ℤ)*(B:ℤ)^(offset+(j+1))=_
    rw [value_update B n (offset+j) (t%B) r.1 (by omega),value_succ,hp]
    change value B n r.1+(r.2:ℤ)*(B:ℤ)^(offset+j)=_ at ih'
    linear_combination ih'+(B:ℤ)^(offset+j)*hd

/-- The five-by-five source uses this row accumulation with width five and
base 10^9. The terminal carry is assigned, exactly as in the C source. -/
def rows (B width : ℕ) (a b : ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => fun _ => 0
  | i+1 =>
    let r := row B i (a i) b (rows B width a b i) width
    Function.update r.1 (i+width) r.2

theorem rows_zero_above (B width : ℕ) (a b : ℕ → ℕ) (i k : ℕ)
    (hk : i+width ≤ k) : rows B width a b i k=0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hne : k≠i+width := by omega
    simp only [rows,Function.update_of_ne hne]
    rw [row_untouched B i (a i) b _ width k (by omega)]
    exact ih (by omega)

/-- Complete exact schoolbook product identity. With base=10^9 and width=5
this supplies the numerical invariant needed by the actual C fixed_multiply
loop, before its drop-four-digits and signed-floor normalization. -/
theorem rows_value (B width : ℕ) (a b : ℕ → ℕ) (i : ℕ) (hi : i ≤ width) :
    value B (2*width) (rows B width a b i)=value B i a*value B width b := by
  induction i with
  | zero => simp [rows,value]
  | succ i ih =>
    have hiw : i < width := by omega
    have ih' := ih (by omega)
    let r := row B i (a i) b (rows B width a b i) width
    have hz : r.1 (i+width)=0 := by
      rw [row_untouched B i (a i) b _ width (i+width) (by omega)]
      exact rows_zero_above B width a b i (i+width) le_rfl
    have hrow := row_value B i (a i) b (rows B width a b i) (2*width) width (by omega)
    change value B (2*width) r.1+(r.2:ℤ)*(B:ℤ)^(i+width)=_ at hrow
    change value B (2*width) (Function.update r.1 (i+width) r.2)=_
    rw [value_update B (2*width) (i+width) r.2 r.1 (by omega),hz]
    rw [value_succ]
    simp only [Nat.cast_zero,sub_zero]
    nlinarith [hrow]

theorem five_by_five_product (a b : ℕ → ℕ) :
    value 1000000000 10 (rows 1000000000 5 a b 5)=
      value 1000000000 5 a*value 1000000000 5 b :=
  rows_value 1000000000 5 a b 5 le_rfl

def magnitude (B n : ℕ) (d : ℕ → ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, d j*B^j

theorem value_eq_magnitude (B n : ℕ) (d : ℕ → ℕ) :
    value B n d=(magnitude B n d:ℤ) := by simp [value,magnitude]

theorem magnitude_succ (B n : ℕ) (d : ℕ → ℕ) :
    magnitude B (n+1) d=magnitude B n d+d n*B^n := Finset.sum_range_succ _ _

theorem magnitude_split (B n m : ℕ) (d : ℕ → ℕ) :
    magnitude B (n+m) d=magnitude B n d+B^n*magnitude B m (fun j => d (n+j)) := by
  unfold magnitude
  rw [Finset.sum_range_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

theorem magnitude_lt (B n : ℕ) (hB : 0 < B) (d : ℕ → ℕ)
    (hd : ∀ j < n, d j < B) : magnitude B n d < B^n := by
  induction n with
  | zero => simp [magnitude]
  | succ n ih =>
    have hn := ih (fun j hj => hd j (by omega))
    have hdn := hd n (by omega)
    have hm := Nat.mul_le_mul_right (B^n) (show d n+1 ≤ B by omega)
    rw [magnitude_succ,pow_succ]
    nlinarith

theorem lost_sum_zero_iff (B n : ℕ) (hB : 0 < B) (d : ℕ → ℕ) :
    (∑ j ∈ Finset.range n, d j)=0 ↔ magnitude B n d=0 := by
  simp only [magnitude,Finset.sum_eq_zero_iff]
  constructor
  · intro h j hj; rw [h j hj,zero_mul]
  · intro h j hj
    exact (mul_eq_zero.mp (h j hj)).resolve_right (ne_of_gt (Nat.pow_pos hB))

theorem product_natural (a b : ℕ → ℕ) :
    magnitude 1000000000 10 (rows 1000000000 5 a b 5)=
      magnitude 1000000000 5 a*magnitude 1000000000 5 b := by
  have h := five_by_five_product a b
  simpa only [value_eq_magnitude,←Nat.cast_mul,Int.natCast_inj] using h

/-- Exact meaning of the source's five output digits after dropping four
low digits. A zero overflow word is a checked application condition. -/
theorem drop_four_digits (B : ℕ) (hB : 0 < B) (d : ℕ → ℕ)
    (hd : ∀ j < 10, d j < B) (hoverflow : d 9=0) :
    magnitude B 10 d/B^4=magnitude B 5 (fun j => d (j+4)) ∧
      magnitude B 10 d%B^4=magnitude B 4 d := by
  have hlow := magnitude_lt B 4 hB d (fun j hj => hd j (by omega))
  have hsplit : magnitude B 10 d=magnitude B 4 d+B^4*magnitude B 5 (fun j => d (j+4)) := by
    rw [show 10=4+6 by decide,magnitude_split,show 6=5+1 by decide,magnitude_split]
    simp only [magnitude,Finset.sum_range_one]
    simp [hoverflow,Nat.add_comm]
  rw [hsplit]
  constructor
  · rw [Nat.add_mul_div_left _ _ (Nat.pow_pos hB),Nat.div_eq_of_lt hlow,zero_add]
  · simp [Nat.add_mod,Nat.mod_eq_of_lt hlow]

/-- The source increments the absolute value exactly when a negative
product lost nonzero low digits. This is Euclidean floor, not truncation
towards zero. All variables here are mathematical integers/digits; the
source contract still must prove the represented inputs and stores. -/
theorem negative_product_floor (P U : ℕ) (hU : 0 < U) :
    (-(P:ℤ))/(U:ℤ)= -((P/U:ℕ):ℤ)-(if P%U=0 then 0 else 1) := by
  have hdiv : (P:ℤ)=((P/U:ℕ):ℤ)*(U:ℤ)+((P%U:ℕ):ℤ) := by
    exact_mod_cast (by nlinarith [Nat.div_add_mod P U] : P=P/U*U+P%U)
  have hrem : ((P%U:ℕ):ℤ) < (U:ℤ) := by exact_mod_cast Nat.mod_lt P hU
  have hrem0 : (0:ℤ) ≤ ((P%U:ℕ):ℤ) := by positivity
  apply (Int.ediv_eq_iff_of_pos (by exact_mod_cast hU : (0:ℤ) < U)).mpr
  by_cases hr : P%U=0
  · simp only [hr,↓reduceIte,sub_zero,Nat.cast_zero,add_zero] at *
    constructor <;> nlinarith
  · have hremp : (0:ℤ) < ((P%U:ℕ):ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero hr)
    simp only [hr,↓reduceIte]
    constructor <;> nlinarith

/-- Mathematical signed value of the C routine's retained five digits and
its negative-product increment. Its separate status reports whether that
increment overflowed the representable output, so source refinement must
keep that applicability condition. -/
def normalizedProduct (B : ℕ) (d : ℕ → ℕ) (negative : Bool) : ℤ :=
  if negative then
    -(magnitude B 5 (fun j => d (j+4)):ℤ)-
      (if (∑ j ∈ Finset.range 4, d j)=0 then 0 else 1)
  else (magnitude B 5 (fun j => d (j+4)):ℤ)

theorem normalizedProduct_eq_floor (B : ℕ) (hB : 0 < B) (d : ℕ → ℕ)
    (hd : ∀ j < 10, d j < B) (hoverflow : d 9=0) (negative : Bool) :
    normalizedProduct B d negative=
      (if negative then -(magnitude B 10 d:ℤ) else (magnitude B 10 d:ℤ))/(B^4:ℕ) := by
  have hdrop := drop_four_digits B hB d hd hoverflow
  have hzero : (∑ j ∈ Finset.range 4, d j)=0 ↔ magnitude B 10 d%B^4=0 := by
    rw [hdrop.2]
    exact lost_sum_zero_iff B 4 hB d
  cases negative with
  | false =>
    simp only [normalizedProduct, Bool.false_eq_true,↓reduceIte]
    change (magnitude B 5 (fun j => d (j+4)):ℤ)=((magnitude B 10 d/B^4:ℕ):ℤ)
    rw [hdrop.1]
  | true =>
    simp only [normalizedProduct,↓reduceIte]
    rw [negative_product_floor _ _ (Nat.pow_pos hB),hdrop.1]
    by_cases hz : (∑ j ∈ Finset.range 4, d j)=0
    · simp only [hz,hzero.mp hz,↓reduceIte]
    · have hnz := mt hzero.mpr hz
      simp only [hz,hnz,↓reduceIte]

#print axioms row_value
#print axioms rows_value
#print axioms five_by_five_product
#print axioms drop_four_digits
#print axioms negative_product_floor
#print axioms normalizedProduct_eq_floor
end RH080Next.FFT.Limbs
