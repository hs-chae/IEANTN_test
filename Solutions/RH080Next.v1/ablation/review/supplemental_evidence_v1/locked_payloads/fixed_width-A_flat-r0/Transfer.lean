import Mathlib

/- Standalone conditional transfer, without application objects in arm A.
   Curve propositions are explicit theorem arguments, not axioms. -/
namespace WidthTransfer
open Filter
open scoped Topology

noncomputable section

def piReal (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊
def rightEnd (c x : ℝ) : ℝ := x + c * Real.sqrt x * Real.log x
def halfOpenCount (c x : ℝ) : ℕ := piReal (rightEnd c x) - piReal x
def normalizedPopulation (c x : ℝ) : ℝ := (halfOpenCount c x : ℝ) / Real.sqrt x
def GoodCoefficient (a c : ℝ) : Prop :=
  0 < c ∧ ∃ d > 0, ∀ᶠ x in atTop, a + d ≤ normalizedPopulation c x

def G (a : ℝ) : ℝ := (20582561296 / 24680948495) * (1 + 2 * a)
def S (a : ℝ) : ℝ := 944247 / 1000000 + (1163388 / 1000000) * a
def F (a : ℝ) : ℝ := 9 / 8 + (16 / 15) * a
def E (a : ℝ) : ℝ := min (G a) (min (S a) (F a))
def u : ℝ := 544470055511653 / 2490320656859788
def v : ℝ := 542259 / 290164
def GaussCurve : Prop := ∀ a : ℝ, 0 ≤ a → ∀ e : ℝ, 0 < e → GoodCoefficient a (G a + e)
def SparseCurve : Prop := ∀ a : ℝ, 0 ≤ a → GoodCoefficient a (S a)
def FlatCurve : Prop := ∀ a : ℝ, 0 ≤ a → GoodCoefficient a (F a)

theorem piReal_mono : Monotone piReal :=
  Nat.monotone_primeCounting.comp Nat.floor_mono

theorem good_mono {a c w : ℝ} (h : GoodCoefficient a c) (hcw : c ≤ w) :
    GoodCoefficient a w := by
  obtain ⟨hc, d, hd, h⟩ := h
  refine ⟨hc.trans_le hcw, d, hd, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hxlog := Real.log_nonneg hx1
  have hy : rightEnd c x ≤ rightEnd w x := by
    unfold rightEnd
    gcongr
  have hn : halfOpenCount c x ≤ halfOpenCount w x :=
    Nat.sub_le_sub_right (piReal_mono hy) _
  exact hx.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr hn) (Real.sqrt_nonneg _))

theorem u_lt_v : u < v := by norm_num [u, v]

theorem G_le_S_iff (a : ℝ) : G a ≤ S a ↔ a ≤ u := by
  unfold G S u
  constructor <;> intro h <;> linarith only [h]

theorem S_le_F_iff (a : ℝ) : S a ≤ F a ↔ a ≤ v := by
  unfold S F v
  constructor <;> intro h <;> linarith only [h]

theorem S_le_G_iff (a : ℝ) : S a ≤ G a ↔ u ≤ a := by
  unfold G S u
  constructor <;> intro h <;> linarith only [h]

theorem F_le_S_iff (a : ℝ) : F a ≤ S a ↔ v ≤ a := by
  unfold S F v
  constructor <;> intro h <;> linarith only [h]

theorem E_gaussian {a : ℝ} (ha : a ≤ u) : E a = G a := by
  have hs := (S_le_F_iff a).mpr (ha.trans u_lt_v.le)
  rw [E, min_eq_left hs, min_eq_left ((G_le_S_iff a).mpr ha)]

theorem E_sparse {a : ℝ} (hu : u ≤ a) (hv : a ≤ v) : E a = S a := by
  rw [E, min_eq_left ((S_le_F_iff a).mpr hv), min_eq_right ((S_le_G_iff a).mpr hu)]

theorem E_flat {a : ℝ} (hv : v ≤ a) : E a = F a := by
  have hs := (F_le_S_iff a).mpr hv
  rw [E, min_eq_right hs,
    min_eq_right (hs.trans ((S_le_G_iff a).mpr (u_lt_v.le.trans hv)))]

theorem good_above_envelope (hg : GaussCurve) (hs : SparseCurve) (hf : FlatCurve)
    {a w : ℝ} (ha : 0 ≤ a) (hw : E a < w) : GoodCoefficient a w := by
  by_cases hu : a ≤ u
  · rw [E_gaussian hu] at hw
    convert hg a ha (w - G a) (sub_pos.mpr hw) using 1; ring
  · by_cases hv : a ≤ v
    · rw [E_sparse (le_of_not_ge hu) hv] at hw
      exact good_mono (hs a ha) hw.le
    · rw [E_flat (le_of_not_ge hv)] at hw
      exact good_mono (hf a ha) hw.le

theorem good_at_envelope (hs : SparseCurve) (hf : FlatCurve)
    {a : ℝ} (ha : 0 ≤ a) (hu : u ≤ a) : GoodCoefficient a (E a) := by
  by_cases hv : a ≤ v
  · rw [E_sparse hu hv]
    exact hs a ha
  · rw [E_flat (le_of_not_ge hv)]
    exact hf a ha

def a3 : ℝ := 685251 / 387796
def a5 : ℝ := 465 / 128

theorem good3 (hs : SparseCurve) : GoodCoefficient a3 3 := by
  have h : S a3 = 3 := by norm_num [S, a3]
  simpa only [h] using hs a3 (by norm_num [a3])

theorem good5 (hf : FlatCurve) : GoodCoefficient a5 5 := by
  have h : F a5 = 5 := by norm_num [F, a5]
  simpa only [h] using hf a5 (by norm_num [a5])

theorem envelope_inversions : E a3 = 3 ∧ E a5 = 5 := by
  rw [E_sparse (a := a3) (by norm_num [u, a3]) (by norm_num [a3, v]),
      E_flat (a := a5) (by norm_num [a5, v])]
  norm_num [S, a3, F, a5]

theorem E_strictMono : StrictMono E := by
  intro a b h
  have hg : G a < G b := by unfold G; linarith only [h]
  have hs : S a < S b := by unfold S; linarith only [h]
  have hf : F a < F b := by unfold F; linarith only [h]
  have hG : E a ≤ G a := min_le_left ..
  have hS : E a ≤ S a := (min_le_right ..).trans (min_le_left ..)
  have hF : E a ≤ F a := (min_le_right ..).trans (min_le_right ..)
  exact lt_min (hG.trans_lt hg) (lt_min (hS.trans_lt hs) (hF.trans_lt hf))

def B (c : ℝ) : ℝ := (8 / 9) * c - 18203 / 20000
def O (a : ℝ) : ℝ := (9 / 8) * (a + 18203 / 20000)

theorem octic_domain (a : ℝ) :
    (103/100 ≤ O a ∧ O a ≤ 16) ↔ (973/180000 ≤ a ∧ a ≤ 2396173/180000) := by
  unfold O
  constructor <;> rintro ⟨h₁,h₂⟩ <;> exact ⟨by linarith only [h₁], by linarith only [h₂]⟩

theorem octic_gain3 : a3 - B 3 = 61212941 / 5816940000 := by norm_num [a3,B]
theorem octic_gain5 : a5 - B 5 = 70933 / 720000 := by norm_num [a5,B]

theorem algebra_width_gain_positive (a : ℝ) : E a < O a := by
  by_cases h₁ : a ≤ u
  · rw [E_gaussian h₁]
    unfold G O
    unfold u at h₁
    linarith only [h₁]
  · by_cases h₂ : a ≤ v
    · rw [E_sparse (le_of_not_ge h₁) h₂]
      unfold S O
      unfold v at h₂
      linarith only [h₂]
    · have hh := le_of_not_ge h₂
      rw [E_flat hh]
      unfold F O
      unfold v at hh
      linarith only [hh]

theorem end_gt_left {c x : ℝ} (hc : 0 < c) (hx : 1 < x) : x < rightEnd c x := by
  unfold rightEnd
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hlog := Real.log_pos hx
  linarith only [mul_pos (mul_pos hc hsq) hlog]

def openPrimes (c x : ℝ) : Finset ℕ :=
  Nat.primesBelow ⌈rightEnd c x⌉₊ \ Nat.primesLE ⌊x⌋₊

def openCount (c x : ℝ) : ℕ := (openPrimes c x).card

theorem mem_openPrimes {c x : ℝ} {p : ℕ} (hx : 0 ≤ x) :
    p ∈ openPrimes c x ↔ p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < rightEnd c x := by
  simp only [openPrimes, Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesLE,
    Nat.lt_ceil, Nat.le_floor_iff hx]
  simp only [not_and_or, not_le]
  tauto

theorem openCount_eq {c x : ℝ} (hx : 0 ≤ x) (hy : x < rightEnd c x) :
    openCount c x = Nat.primeCounting' ⌈rightEnd c x⌉₊ - piReal x := by
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesBelow ⌈rightEnd c x⌉₊ := by
    intro p hp
    rw [Nat.mem_primesLE, Nat.le_floor_iff hx] at hp
    exact Nat.mem_primesBelow.mpr ⟨Nat.lt_ceil.mpr (hp.1.trans_lt hy), hp.2⟩
  simp [openCount, openPrimes, Finset.card_sdiff_of_subset hsub,
    Nat.primesBelow_card_eq_primeCounting', piReal]

theorem endpoint_loss {c x : ℝ} (hx : 0 ≤ x) (hy : x < rightEnd c x) :
    halfOpenCount c x ≤ openCount c x + 1 := by
  rw [openCount_eq hx hy, halfOpenCount]
  have hfloor : ⌊rightEnd c x⌋₊ ≤ ⌈rightEnd c x⌉₊ := Nat.floor_le_ceil _
  have hmono := Nat.monotone_primeCounting' hfloor
  have hstep : piReal (rightEnd c x) ≤ Nat.primeCounting' ⌊rightEnd c x⌋₊ + 1 := by
    unfold piReal Nat.primeCounting Nat.primeCounting'
    rw [Nat.count_succ]
    split <;> omega
  omega

def GoodStrict (a c : ℝ) : Prop :=
  0 < c ∧ ∃ d > 0, ∀ᶠ x in atTop, a + d ≤ (openCount c x : ℝ) / Real.sqrt x

theorem strict_of_good {a c : ℝ} (h : GoodCoefficient a c) : GoodStrict a c := by
  obtain ⟨hc, d, hd, h⟩ := h
  refine ⟨hc, d / 2, by positivity, ?_⟩
  have hlarge : ∀ᶠ x : ℝ in atTop, 2 / d ≤ Real.sqrt x :=
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (2 / d : ℝ))
  filter_upwards [h, hlarge, eventually_gt_atTop (1 : ℝ)] with x hpop hsq hx
  have hsqpos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hnat := endpoint_loss (by linarith) (end_gt_left hc hx)
  have hreal : (halfOpenCount c x : ℝ) ≤ (openCount c x : ℝ) + 1 := by exact_mod_cast hnat
  have hsmall : 1 / Real.sqrt x ≤ d / 2 := by
    apply (div_le_iff₀ hsqpos).mpr
    have hh := (div_le_iff₀ hd).mp hsq
    linarith only [hh]
  change a + d ≤ (halfOpenCount c x : ℝ) / Real.sqrt x at hpop
  have hquot := div_le_div_of_nonneg_right hreal hsqpos.le
  rw [add_div] at hquot
  linarith only [hpop,hquot,hsmall]

theorem strict3 (hs : SparseCurve) : GoodStrict a3 3 := strict_of_good (good3 hs)
theorem strict5 (hf : FlatCurve) : GoodStrict a5 5 := strict_of_good (good5 hf)

theorem piReal_nth (k : ℕ) : piReal (Nat.nth Nat.Prime k) = k + 1 := by
  unfold piReal
  rw [Nat.floor_natCast]
  change Nat.count Nat.Prime (Nat.nth Nat.Prime k + 1) = _
  rw [Nat.count_succ, if_pos (Nat.prime_nth_prime k)]
  exact congrArg (· + 1) (Nat.primeCounting'_nth_eq k)

theorem strict_rank {c x : ℝ} {m : ℕ} (hx : 0 ≤ x) (hy : x < rightEnd c x)
    (hm : m < openCount c x) :
    x < (Nat.nth Nat.Prime (piReal x + m) : ℝ) ∧
      (Nat.nth Nat.Prime (piReal x + m) : ℝ) < rightEnd c x := by
  constructor
  · by_contra! h
    have hle := piReal_mono h
    rw [piReal_nth] at hle
    omega
  · rw [openCount_eq hx hy] at hm
    apply Nat.lt_ceil.mp (Nat.nth_lt_of_lt_count (p := Nat.Prime) ?_)
    change piReal x + m < Nat.primeCounting' ⌈rightEnd c x⌉₊
    omega

#print axioms good_above_envelope
#print axioms good_at_envelope
#print axioms envelope_inversions
#print axioms strict3
#print axioms strict5
#print axioms strict_rank
#print axioms octic_gain3
#print axioms octic_gain5
#print axioms algebra_width_gain_positive

end
end WidthTransfer
