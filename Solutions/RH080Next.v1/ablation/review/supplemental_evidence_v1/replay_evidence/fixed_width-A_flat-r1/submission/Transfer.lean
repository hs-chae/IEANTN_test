import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/- A-flat transfer. Input curve statements are explicit local premises,
not axiom declarations and not imports of unavailable application modules. -/
namespace Transfer
open Filter
open scoped Nat

noncomputable def piReal (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊
noncomputable def endpoint (c x : ℝ) : ℝ := x + c * Real.sqrt x * Real.log x
noncomputable def halfOpenCount (c x : ℝ) : ℕ := piReal (endpoint c x) - piReal x
noncomputable def normalizedPopulation (c x : ℝ) : ℝ :=
  (halfOpenCount c x : ℝ) / Real.sqrt x
def GoodCoefficient (a c : ℝ) : Prop :=
  0 < c ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x : ℝ in atTop,
    a + δ ≤ normalizedPopulation c x

noncomputable def q : ℝ := 20582561296 / 24680948495
noncomputable def gauss (a : ℝ) : ℝ := q * (1 + 2 * a)
noncomputable def sparse (a : ℝ) : ℝ := 944247/1000000 + (1163388/1000000)*a
noncomputable def flat (a : ℝ) : ℝ := 9/8 + (16/15)*a
def GaussianCurve : Prop :=
  ∀ a ≥ 0, ∀ ε > 0, GoodCoefficient a (gauss a + ε)
def SparseCurve : Prop := ∀ a ≥ 0, GoodCoefficient a (sparse a)
def FlatCurve : Prop := ∀ a ≥ 0, GoodCoefficient a (flat a)

theorem width_three (s : SparseCurve) : GoodCoefficient (685251/387796) 3 := by
  have h := s (685251/387796) (by norm_num)
  have he : sparse (685251/387796) = 3 := by norm_num [sparse]
  rwa [he] at h

theorem width_five (f : FlatCurve) : GoodCoefficient (465/128) 5 := by
  have h := f (465/128) (by norm_num)
  have he : flat (465/128) = 5 := by norm_num [flat]
  rwa [he] at h

noncomputable def u : ℝ := 544470055511653/2490320656859788
noncomputable def v : ℝ := 542259/290164
noncomputable def envelope (a : ℝ) : ℝ :=
  if a < u then gauss a else if a < v then sparse a else flat a
theorem thresholds : 0 < u ∧ u < v := by norm_num [u, v]
theorem gauss_lt_sparse (a : ℝ) : gauss a < sparse a ↔ a < u := by
  unfold gauss q sparse u
  constructor <;> intro h <;> linarith
theorem sparse_lt_flat (a : ℝ) : sparse a < flat a ↔ a < v := by
  unfold sparse flat v
  constructor <;> intro h <;> linarith
theorem ties :
    gauss u = 3731134672774344/3112900821074735 ∧
    sparse u = gauss u ∧ sparse v = 9048441/2901640 ∧ flat v = sparse v := by
  norm_num [gauss, q, sparse, flat, u, v]
theorem envelope_eq (a : ℝ) :
    envelope a = min (gauss a) (min (sparse a) (flat a)) := by
  unfold envelope
  split
  · rename_i hu
    have hs := (gauss_lt_sparse a).mpr hu
    have hf := (sparse_lt_flat a).mpr (hu.trans thresholds.2)
    rw [min_eq_left hf.le, min_eq_left hs.le]
  · rename_i hu
    have hs : sparse a ≤ gauss a :=
      le_of_not_gt (fun h => hu ((gauss_lt_sparse a).mp h))
    split
    · rename_i hv
      rw [min_eq_left ((sparse_lt_flat a).mpr hv).le, min_eq_right hs]
    · rename_i hv
      have hf : flat a ≤ sparse a :=
        le_of_not_gt (fun h => hv ((sparse_lt_flat a).mp h))
      rw [min_eq_right hf, min_eq_right (hf.trans hs)]

theorem endpoint_mono {c d x : ℝ} (hx : 1 ≤ x) (hcd : c ≤ d) :
    endpoint c x ≤ endpoint d x :=
  add_le_add_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcd (Real.sqrt_nonneg x)) (Real.log_nonneg hx)) x

theorem population_mono {c d x : ℝ} (hx : 1 ≤ x) (hcd : c ≤ d) :
    normalizedPopulation c x ≤ normalizedPopulation d x := by
  unfold normalizedPopulation halfOpenCount piReal
  exact div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (Nat.sub_le_sub_right
      (Nat.monotone_primeCounting (Nat.floor_mono (endpoint_mono hx hcd))) _))
    (Real.sqrt_nonneg _)

theorem widen {a c d : ℝ} (h : GoodCoefficient a c) (hcd : c ≤ d) :
    GoodCoefficient a d := by
  obtain ⟨hc, δ, hδ, hm⟩ := h
  refine ⟨hc.trans_le hcd, δ, hδ, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), hm] with x hx hmx
  exact hmx.trans (population_mono hx hcd)

theorem envelope_attained (s : SparseCurve) (f : FlatCurve)
    {a c : ℝ} (ha : u ≤ a) (hc : envelope a ≤ c) : GoodCoefficient a c := by
  apply widen _ hc
  unfold envelope
  rw [ite_eq_right (not_lt_of_ge ha)]
  split
  · exact s a (thresholds.1.le.trans ha)
  · exact f a (thresholds.1.le.trans ha)

theorem envelope_above (g : GaussianCurve) (s : SparseCurve) (f : FlatCurve)
    {a c : ℝ} (ha : 0 ≤ a) (hc : envelope a < c) : GoodCoefficient a c := by
  by_cases hu : a < u
  · have he : envelope a = gauss a := ite_eq_left hu
    rw [he] at hc
    simpa only [add_sub_cancel] using g a ha (c - gauss a) (sub_pos.mpr hc)
  · exact envelope_attained s f (le_of_not_gt hu) hc.le

noncomputable def halfPrimes (x y : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊y⌋₊ \ Nat.primesLE ⌊x⌋₊

theorem card_halfPrimes {x y : ℝ} (hxy : x ≤ y) :
    (halfPrimes x y).card = piReal y - piReal x := by
  simp [halfPrimes, piReal, Finset.card_sdiff_of_subset (Nat.primesLE_mono (Nat.floor_mono hxy))]

theorem mem_halfPrimes {p : ℕ} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    p ∈ halfPrimes x y ↔ p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  simp only [halfPrimes, Finset.mem_sdiff, Nat.mem_primesLE, Nat.le_floor_iff hx,
    Nat.le_floor_iff hy]
  constructor
  · rintro ⟨⟨hu, hp⟩, hn⟩
    exact ⟨hp, lt_of_not_ge (fun hl => hn ⟨hl, hp⟩), hu⟩
  · rintro ⟨hp, hl, hu⟩
    exact ⟨⟨hu, hp⟩, fun h => hl.not_ge h.1⟩

noncomputable def openPrimes (x y : ℝ) : Finset ℕ := by
  classical
  exact (halfPrimes x y).filter (fun p => (p : ℝ) < y)

theorem mem_openPrimes {p : ℕ} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    p ∈ openPrimes x y ↔ p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < y := by
  classical
  rw [openPrimes, Finset.mem_filter, mem_halfPrimes hx hy]
  constructor
  · rintro ⟨⟨hp, hl, _⟩, hu⟩
    exact ⟨hp, hl, hu⟩
  · rintro ⟨hp, hl, hu⟩
    exact ⟨⟨hp, hl, hu.le⟩, hu⟩

theorem endpoint_loss {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    piReal y - piReal x ≤ (openPrimes x y).card + 1 := by
  classical
  let A := halfPrimes x y
  let B := openPrimes x y
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have atMostOne : (A \ B).card ≤ 1 := by
    have eq_endpoint : ∀ p ∈ A \ B, (p : ℝ) = y := by
      intro p hp
      obtain ⟨ha, hb⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hprime, hl, hu⟩ := (mem_halfPrimes hx (hx.trans hxy)).mp ha
      apply hu.antisymm
      apply le_of_not_gt
      intro hlt
      exact hb ((mem_openPrimes hx (hx.trans hxy)).mpr ⟨hprime, hl, hlt⟩)
    apply Finset.card_le_one.mpr
    intro p hp r hr
    exact_mod_cast (eq_endpoint p hp).trans (eq_endpoint r hr).symm
  have hsum := Finset.card_sdiff_add_card_eq_card hBA
  have hc : A.card = piReal y - piReal x := card_halfPrimes hxy
  change piReal y - piReal x ≤ B.card + 1
  omega

noncomputable def openNormalized (c x : ℝ) : ℝ :=
  ((openPrimes x (endpoint c x)).card : ℝ) / Real.sqrt x

theorem strict_open {a c : ℝ} (h : GoodCoefficient a c) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ x : ℝ in atTop, a + η ≤ openNormalized c x := by
  obtain ⟨hc, δ, hδ, hm⟩ := h
  refine ⟨δ/2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop ((2/δ)^2), hm]
    with x hx hxlarge hmx
  have h0 : 0 < x := zero_lt_one.trans_le hx
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr h0
  have hxy : x ≤ endpoint c x := by
    have hpos := mul_nonneg (mul_nonneg hc.le (Real.sqrt_nonneg x)) (Real.log_nonneg hx)
    exact le_add_of_nonneg_right hpos
  have hl := endpoint_loss h0.le hxy
  change halfOpenCount c x ≤ _ at hl
  have hl' : (halfOpenCount c x : ℝ) ≤ (openPrimes x (endpoint c x)).card + 1 := by
    exact_mod_cast hl
  have hs := Real.le_sqrt_of_sq_le hxlarge
  have hd : 1 ≤ δ / 2 * Real.sqrt x := by
    have hh := (div_le_iff₀ hδ).mp hs
    linarith
  have hm' := (le_div_iff₀ hsq).mp hmx
  apply (le_div_iff₀ hsq).mpr
  linarith only [hm', hl', hd]

theorem three_open (s : SparseCurve) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ x : ℝ in atTop, 685251/387796 + η ≤ openNormalized 3 x :=
  strict_open (width_three s)

theorem five_open (f : FlatCurve) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ x : ℝ in atTop, 465/128 + η ≤ openNormalized 5 x :=
  strict_open (width_five f)


theorem good_of_lower_alpha {a b c : ℝ} (hab : a ≤ b) (h : GoodCoefficient b c) :
    GoodCoefficient a c := by
  obtain ⟨hc, δ, hδ, hm⟩ := h
  exact ⟨hc, δ, hδ, hm.mono (fun x hx => (add_le_add_left hab δ).trans hx)⟩

theorem gaussian_at_leading_width_below_target (g : GaussianCurve)
    {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) : GoodCoefficient b (gauss a) := by
  have hq : 0 < q := by norm_num [q]
  have hlt : gauss b < gauss a := by
    unfold gauss
    gcongr
  simpa only [add_sub_cancel] using g b hb (gauss a - gauss b) (sub_pos.mpr hlt)

-- A liminf lower-bound formulation without claiming an eventual inequality
-- at the limiting target: each strictly smaller real target has its own tail.
theorem gaussian_leading_open_approximation (g : GaussianCurve)
    {a b : ℝ} (hba : b < a) :
    ∀ᶠ x : ℝ in atTop, b < openNormalized (gauss a) x := by
  by_cases hb : 0 ≤ b
  · obtain ⟨η, hη, hm⟩ := strict_open (gaussian_at_leading_width_below_target g hb hba)
    exact hm.mono (fun x hx => (lt_add_of_pos_right b hη).trans_le hx)
  · apply Eventually.of_forall
    intro x
    exact (lt_of_not_ge hb).trans_le (by unfold openNormalized; positivity)

noncomputable def gInv (c : ℝ) : ℝ := (c / q - 1) / 2
noncomputable def sInv (c : ℝ) : ℝ := (c - 944247/1000000)/(1163388/1000000)
noncomputable def fInv (c : ℝ) : ℝ := (c - 9/8)/(16/15)
noncomputable def inverseEnvelope (c : ℝ) : ℝ := max (gInv c) (max (sInv c) (fInv c))

theorem inverse_fixed :
    gInv 3 = 53460284189/41165122592 ∧ sInv 3 = 685251/387796 ∧ fInv 3 = 225/128 ∧
    gInv 5 = 102822181179/41165122592 ∧ sInv 5 = 4055753/1163388 ∧ fInv 5 = 465/128 := by
  norm_num [gInv, q, sInv, fInv]

theorem fixed_best :
    inverseEnvelope 3 = 685251/387796 ∧ inverseEnvelope 5 = 465/128 := by
  norm_num [inverseEnvelope, gInv, q, sInv, fInv, max_def]

theorem gInv_iff (a c : ℝ) : gauss a ≤ c ↔ a ≤ gInv c := by
  unfold gauss gInv q
  constructor <;> intro h <;> linarith

theorem sInv_iff (a c : ℝ) : sparse a ≤ c ↔ a ≤ sInv c := by
  unfold sparse sInv
  constructor <;> intro h <;> linarith

theorem fInv_iff (a c : ℝ) : flat a ≤ c ↔ a ≤ fInv c := by
  unfold flat fInv
  constructor <;> intro h <;> linarith

theorem envelope_inverse (a c : ℝ) : envelope a ≤ c ↔ a ≤ inverseEnvelope c := by
  simp [envelope_eq, inverseEnvelope, min_le_iff, le_max_iff, gInv_iff, sInv_iff, fInv_iff]

noncomputable def w₁ : ℝ := 3731134672774344/3112900821074735
noncomputable def w₂ : ℝ := 9048441/2901640

theorem inverse_piecewise (c : ℝ) :
    inverseEnvelope c = if c < w₁ then gInv c else if c < w₂ then sInv c else fInv c := by
  have hgs : sInv c ≤ gInv c ↔ c ≤ w₁ := by
    unfold sInv gInv q w₁
    constructor <;> intro h <;> linarith
  have hsf : fInv c ≤ sInv c ↔ c ≤ w₂ := by
    unfold sInv fInv w₂
    constructor <;> intro h <;> linarith
  have hsg : gInv c ≤ sInv c ↔ w₁ ≤ c := by
    unfold sInv gInv q w₁
    constructor <;> intro h <;> linarith
  have hfs : sInv c ≤ fInv c ↔ w₂ ≤ c := by
    unfold sInv fInv w₂
    constructor <;> intro h <;> linarith
  have hw : w₁ < w₂ := by norm_num [w₁, w₂]
  unfold inverseEnvelope
  split
  · rename_i h
    rw [max_eq_left ((hsf.mpr (h.trans hw).le)), max_eq_left (hgs.mpr h.le)]
  · rename_i h
    have hs := hsg.mpr (le_of_not_gt h)
    split
    · rename_i h₂
      rw [max_eq_left (hsf.mpr h₂.le), max_eq_right hs]
    · rename_i h₂
      have hf := hfs.mpr (le_of_not_gt h₂)
      rw [max_eq_right hf, max_eq_right (hs.trans hf)]

noncomputable def octicLeading (c : ℝ) : ℝ := (8/9)*c - 18203/20000
noncomputable def octicInverse (a : ℝ) : ℝ := (9/8)*(a + 18203/20000)

theorem octic_fixed :
    octicLeading 3 = 105391/60000 ∧ octicLeading 5 = 636173/180000 ∧
    inverseEnvelope 3 - octicLeading 3 = 61212941/5816940000 ∧
    inverseEnvelope 5 - octicLeading 5 = 70933/720000 := by
  rw [fixed_best.1, fixed_best.2]
  norm_num [octicLeading]

theorem octic_domain (a : ℝ) :
    (103/100 ≤ octicInverse a ∧ octicInverse a ≤ 16) ↔
    (973/180000 ≤ a ∧ a ≤ 2396173/180000) := by
  unfold octicInverse
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem savings_positive {a : ℝ} (_ : 973/180000 ≤ a) (_ : a ≤ 2396173/180000) :
    envelope a < octicInverse a := by
  unfold envelope
  split
  · rename_i h
    unfold gauss q octicInverse
    unfold u at h
    linarith
  · split
    · rename_i h
      unfold sparse octicInverse
      unfold v at h
      linarith
    · rename_i h
      have hh := le_of_not_gt h
      unfold v at hh
      unfold flat octicInverse
      linarith

theorem pc_nth (n : ℕ) : piReal (Nat.nth Nat.Prime n : ℝ) = n + 1 := by
  simp only [piReal, Nat.floor_natCast, Nat.primeCounting, Nat.primeCounting',
    Nat.count_succ, Nat.prime_nth_prime, ite_true]
  have hh := Nat.primeCounting'_nth_eq n
  exact congrArg (· + 1) hh

theorem rank_of_halfCount {n k : ℕ} {y : ℝ}
    (h : k ≤ piReal y - piReal (Nat.nth Nat.Prime n : ℝ)) (hk : 0 < k) :
    (Nat.nth Nat.Prime (n+k) : ℝ) ≤ y := by
  rw [pc_nth] at h
  have hpi : n+k < piReal y := by omega
  have hlt : Nat.nth Nat.Prime (n+k) < ⌊y⌋₊ + 1 := Nat.nth_lt_of_lt_count hpi
  exact (Nat.le_floor_iff' (Nat.prime_nth_prime _).ne_zero).mp (by omega)

-- The strict endpoint follows by bounding the (m+1)-st prime after p_n.
theorem rank_strict {a c : ℝ} (h : GoodCoefficient a c) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m →
      (m : ℝ) ≤ a * Real.sqrt (Nat.nth Nat.Prime n : ℝ) →
      (Nat.nth Nat.Prime n : ℝ) < (Nat.nth Nat.Prime (n+m) : ℝ) ∧
      (Nat.nth Nat.Prime (n+m) : ℝ) < endpoint c (Nat.nth Nat.Prime n : ℝ) := by
  obtain ⟨_, δ, hδ, hp⟩ := h
  obtain ⟨T, hT⟩ := eventually_atTop.mp hp
  filter_upwards [eventually_ge_atTop ⌈T⌉₊] with n hn
  let x : ℝ := Nat.nth Nat.Prime n
  have hge : T ≤ x := calc
    T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ x := by dsimp [x]; exact_mod_cast (show n ≤ Nat.nth Nat.Prime n from
      (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n))
  have hpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr
    (Nat.cast_pos.mpr (Nat.prime_nth_prime n).pos)
  have hh := (le_div_iff₀ hpos).mp (hT x hge)
  have hs := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  intro m hm hma
  have hlt : (m : ℝ) < halfOpenCount c x :=
    hma.trans_lt (lt_of_lt_of_le (by nlinarith only [mul_pos hδ hpos]) hh)
  have hm' : m+1 ≤ halfOpenCount c x := by
    have hh' : m < halfOpenCount c x := by exact_mod_cast hlt
    omega
  have hub := rank_of_halfCount (n:=n) (k:=m+1) (y:=endpoint c x) hm' (by omega)
  have hstep : (Nat.nth Nat.Prime (n+m) : ℝ) < (Nat.nth Nat.Prime (n+(m+1)) : ℝ) := by
    exact_mod_cast hs (show n+m < n+(m+1) by omega)
  refine ⟨?_, hstep.trans_le hub⟩
  exact_mod_cast hs (show n < n+m by omega)

end Transfer

#print axioms Transfer.width_three
#print axioms Transfer.width_five
#print axioms Transfer.three_open
#print axioms Transfer.five_open
#print axioms Transfer.envelope_above
#print axioms Transfer.envelope_attained
#print axioms Transfer.inverse_piecewise
#print axioms Transfer.savings_positive
#print axioms Transfer.rank_strict
