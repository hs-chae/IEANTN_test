import RH080EstimatePack

open Filter
open scoped Topology
open IEANTN.CMSFunctional

namespace PopulationTransfer

noncomputable section

def q : ℝ := 20582561296 / 24680948495
def G (a : ℝ) : ℝ := q * (1 + 2 * a)
def S (a : ℝ) : ℝ := 944247 / 1000000 + (1163388 / 1000000) * a
def F (a : ℝ) : ℝ := 9 / 8 + (16 / 15) * a
def u : ℝ := 544470055511653 / 2490320656859788
def v : ℝ := 542259 / 290164
def w : ℝ := 172404138261 / 356130660736
def U : ℝ := 3731134672774344 / 3112900821074735
def V : ℝ := 9048441 / 2901640
def a3 : ℝ := 685251 / 387796
def a5 : ℝ := 465 / 128

def envelope (a : ℝ) : ℝ := min (G a) (min (S a) (F a))

/-- The region furnished by direct curve applications and widening, not a
    characterization of the unknown actual good coefficients. -/
def direct (a c : ℝ) : Prop := G a < c ∨ S a ≤ c ∨ F a ≤ c

theorem cross_order : 0 < u ∧ u < w ∧ w < v := by
  norm_num [u, w, v]

theorem G_sub_S (a : ℝ) : G a - S a = (2*q - 1163388/1000000)*(a-u) := by
  unfold G S u q
  ring

theorem S_sub_F (a : ℝ) : S a - F a = (1163388/1000000 - 16/15)*(a-v) := by
  unfold S F v
  ring

theorem G_sub_F (a : ℝ) : G a - F a = (2*q - 16/15)*(a-w) := by
  unfold G F q w
  ring

theorem G_le_S (a : ℝ) : G a ≤ S a ↔ a ≤ u := by
  have h : (0:ℝ) < 2*q - 1163388/1000000 := by norm_num [q]
  rw [← sub_nonpos, G_sub_S]
  constructor
  · intro hm
    by_contra! hb
    exact (not_lt_of_ge hm) (mul_pos h (sub_pos.mpr hb))
  · exact fun hb => mul_nonpos_of_nonneg_of_nonpos h.le (sub_nonpos.mpr hb)

theorem S_le_F (a : ℝ) : S a ≤ F a ↔ a ≤ v := by
  have h : (0:ℝ) < 1163388/1000000 - 16/15 := by norm_num
  rw [← sub_nonpos, S_sub_F]
  constructor
  · intro hm
    by_contra! hb
    exact (not_lt_of_ge hm) (mul_pos h (sub_pos.mpr hb))
  · exact fun hb => mul_nonpos_of_nonneg_of_nonpos h.le (sub_nonpos.mpr hb)

theorem S_le_G (a : ℝ) : S a ≤ G a ↔ u ≤ a := by
  have h : (0:ℝ) < 2*q - 1163388/1000000 := by norm_num [q]
  rw [← sub_nonneg, G_sub_S, mul_nonneg_iff_of_pos_left h, sub_nonneg]

theorem F_le_S (a : ℝ) : F a ≤ S a ↔ v ≤ a := by
  have h : (0:ℝ) < 1163388/1000000 - 16/15 := by norm_num
  rw [← sub_nonneg, S_sub_F, mul_nonneg_iff_of_pos_left h, sub_nonneg]

theorem middle_cross : G w = F w ∧ S w < G w := by
  constructor
  · have h := G_sub_F w
    simp at h
    exact sub_eq_zero.mp h
  · exact lt_of_not_ge (fun h => (not_le_of_gt cross_order.2.1) ((G_le_S w).mp h))

theorem envelope_left {a : ℝ} (h : a ≤ u) : envelope a = G a := by
  have huv : u ≤ v := (cross_order.2.1.trans cross_order.2.2).le
  have hGS := (G_le_S a).mpr h
  have hSF := (S_le_F a).mpr (h.trans huv)
  exact min_eq_left (le_min hGS (hGS.trans hSF))

theorem envelope_middle {a : ℝ} (h₁ : u ≤ a) (h₂ : a ≤ v) : envelope a = S a := by
  unfold envelope
  rw [min_eq_left ((S_le_F a).mpr h₂), min_eq_right ((S_le_G a).mpr h₁)]

theorem envelope_right {a : ℝ} (h : v ≤ a) : envelope a = F a := by
  have huv : u ≤ v := (cross_order.2.1.trans cross_order.2.2).le
  have hFS := (F_le_S a).mpr h
  unfold envelope
  rw [min_eq_right hFS, min_eq_right (hFS.trans ((S_le_G a).mpr (huv.trans h)))]

theorem direct_left {a c : ℝ} (h : a < u) : direct a c ↔ envelope a < c := by
  have hGS : G a < S a := lt_of_not_ge (fun h' => (not_le_of_gt h) ((S_le_G a).mp h'))
  have huv : u < v := cross_order.2.1.trans cross_order.2.2
  have hSF := (S_le_F a).mpr (h.trans huv).le
  rw [envelope_left h.le]
  constructor
  · rintro (hG | hS | hF)
    · exact hG
    · exact hGS.trans_le hS
    · exact (hGS.trans_le hSF).trans_le hF
  · exact Or.inl

theorem direct_middle {a c : ℝ} (h₁ : u ≤ a) (h₂ : a ≤ v) :
    direct a c ↔ envelope a ≤ c := by
  rw [envelope_middle h₁ h₂]
  constructor
  · rintro (hG | hS | hF)
    · exact ((S_le_G a).mpr h₁).trans hG.le
    · exact hS
    · exact ((S_le_F a).mpr h₂).trans hF
  · exact fun h => Or.inr (Or.inl h)

theorem direct_right {a c : ℝ} (h : v ≤ a) : direct a c ↔ envelope a ≤ c := by
  have huv : u ≤ v := (cross_order.2.1.trans cross_order.2.2).le
  have hFS := (F_le_S a).mpr h
  rw [envelope_right h]
  constructor
  · rintro (hG | hS | hF)
    · exact (hFS.trans ((S_le_G a).mpr (huv.trans h))).trans hG.le
    · exact hFS.trans hS
    · exact hF
  · exact fun h => Or.inr (Or.inr h)

theorem direct_inf (a : ℝ) : sInf {c : ℝ | direct a c} = envelope a := by
  rcases lt_or_ge a u with h | h
  · rw [show {c : ℝ | direct a c} = Set.Ioi (envelope a) from Set.ext fun _ => direct_left h]
    exact csInf_Ioi
  · have hiff : ∀ c, direct a c ↔ envelope a ≤ c := fun c =>
      if h' : a ≤ v then direct_middle h h' else direct_right (le_of_not_ge h')
    rw [show {c : ℝ | direct a c} = Set.Ici (envelope a) from Set.ext hiff]
    exact csInf_Ici

theorem ofG (hCMS : CMSFunctionalInput.v1.population_reduction)
    (rh : RiemannHypothesis) {a c : ℝ} (ha : 0 ≤ a) (hc : G a < c) :
    GoodCoefficient a c := by
  have h := RH080Exposure.Estimates.gaussian hCMS rh a ha (c-G a) (sub_pos.mpr hc)
  change GoodCoefficient a (G a + (c-G a)) at h
  rwa [show G a + (c-G a) = c by ring] at h

theorem ofS (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis)
    {a c : ℝ} (ha : 0 ≤ a) (hc : S a ≤ c) : GoodCoefficient a c :=
  RHOnePrime.CMSFunctional.goodCoefficient_mono
    (RH080Exposure.Estimates.sparse hNorm hUniform rh a ha) hc

theorem ofF (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis)
    {a c : ℝ} (ha : 0 ≤ a) (hc : F a ≤ c) : GoodCoefficient a c :=
  RHOnePrime.CMSFunctional.goodCoefficient_mono
    (RH080Exposure.Estimates.flat hNorm hUniform rh a ha) hc

theorem of_direct (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis)
    {a c : ℝ} (ha : 0 ≤ a) (hc : direct a c) : GoodCoefficient a c := by
  rcases hc with h | h | h
  · exact ofG hCMS rh ha h
  · exact ofS hNorm hUniform rh ha h
  · exact ofF hNorm hUniform rh ha h

theorem infGood_le_envelope (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis)
    {a : ℝ} (ha : 0 ≤ a) :
    sInf (goodCoefficients a) ≤ envelope a := by
  have hb : BddBelow (goodCoefficients a) := ⟨0, fun _ h => h.1.le⟩
  rw [← direct_inf a]
  apply le_csInf
  · exact ⟨S a, Or.inr (Or.inl le_rfl)⟩
  · exact fun c hc => csInf_le hb (of_direct hCMS hNorm hUniform rh ha (show direct a c from hc))

theorem widths : G u = U ∧ S u = U ∧ S v = V ∧ F v = V ∧ q < U ∧ U < 3 ∧ 3 < V ∧ V < 5 := by
  norm_num [G, S, F, q, u, v, U, V]

theorem good_three (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis) :
    GoodCoefficient a3 3 := ofS hNorm hUniform rh (by norm_num [a3]) (by norm_num [S,a3])

theorem good_five (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis) :
    GoodCoefficient a5 5 := ofF hNorm hUniform rh (by norm_num [a5]) (by norm_num [F,a5])

theorem direct_three (a : ℝ) : direct a 3 ↔ a ≤ a3 := by
  unfold direct G S F a3 q
  constructor
  · rintro (h | h | h) <;> linarith
  · intro h
    right; left
    linarith

theorem direct_five (a : ℝ) : direct a 5 ↔ a ≤ a5 := by
  unfold direct G S F a5 q
  constructor
  · rintro (h | h | h) <;> linarith
  · intro h
    right; right
    linarith


def endpoint (c x : ℝ) : ℝ := x + c * Real.sqrt x * Real.log x

/-- Exact finite set of primes in the half-open interval (for 0 ≤ x ≤ y). -/
def halfPrimes (x y : ℝ) : Finset ℕ := (Nat.primesLE ⌊y⌋₊) \ (Nat.primesLE ⌊x⌋₊)

/-- Exact finite set of primes in the open interval (for 0 ≤ x). -/
def openPrimes (x y : ℝ) : Finset ℕ := (Nat.primesBelow ⌈y⌉₊) \ (Nat.primesLE ⌊x⌋₊)

def openCount (c x : ℝ) : ℕ := (openPrimes x (endpoint c x)).card

theorem mem_halfPrimes {x y : ℝ} {p : ℕ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    p ∈ halfPrimes x y ↔ Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  simp only [halfPrimes, Finset.mem_sdiff, Nat.mem_primesLE,
    Nat.le_floor_iff hx, Nat.le_floor_iff hy]
  constructor
  · rintro ⟨⟨hpy, hp⟩, hn⟩
    exact ⟨hp, lt_of_not_ge (fun h => hn ⟨h,hp⟩), hpy⟩
  · rintro ⟨hp, hxp, hpy⟩
    exact ⟨⟨hpy,hp⟩, fun h => (not_le_of_gt hxp) h.1⟩

theorem mem_openPrimes {x y : ℝ} {p : ℕ} (hx : 0 ≤ x) :
    p ∈ openPrimes x y ↔ Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) < y := by
  simp only [openPrimes, Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesLE,
    Nat.lt_ceil, Nat.le_floor_iff hx]
  constructor
  · rintro ⟨⟨hpy, hp⟩, hn⟩
    exact ⟨hp, lt_of_not_ge (fun h => hn ⟨h,hp⟩), hpy⟩
  · rintro ⟨hp, hxp, hpy⟩
    exact ⟨⟨hpy,hp⟩, fun h => (not_le_of_gt hxp) h.1⟩

theorem halfPrimes_card {x y : ℝ} (hxy : x ≤ y) :
    (halfPrimes x y).card = piReal y - piReal x := by
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊y⌋₊ := by
    intro p hp
    obtain ⟨hpx, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpx.trans (Nat.floor_mono hxy),hp⟩
  simp only [halfPrimes, Finset.card_sdiff_of_subset hsub, Nat.primesLE_card_eq_primeCounting, piReal]

theorem openPrimes_card {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    (openPrimes x y).card = Nat.primeCounting' ⌈y⌉₊ - piReal x := by
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesBelow ⌈y⌉₊ := by
    intro p hp
    obtain ⟨hpx, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesBelow.mpr ⟨Nat.lt_ceil.mpr (((Nat.le_floor_iff hx).mp hpx).trans_lt hxy),hp⟩
  simp only [openPrimes, Finset.card_sdiff_of_subset hsub,
    Nat.primesLE_card_eq_primeCounting, Nat.primesBelow_card_eq_primeCounting', piReal]

theorem halfPrimes_subset_insert {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    halfPrimes x y ⊆ insert ⌊y⌋₊ (openPrimes x y) := by
  intro p hp
  obtain ⟨hp, hxp, hpy⟩ := (mem_halfPrimes hx (hx.trans hxy)).mp hp
  rcases lt_or_eq_of_le hpy with h | h
  · exact Finset.mem_insert_of_mem ((mem_openPrimes hx).mpr ⟨hp,hxp,h⟩)
  · have he : ⌊y⌋₊ = p := by rw [← h, Nat.floor_natCast]
    rw [he]
    exact Finset.mem_insert_self _ _

theorem endpoint_lt {c x : ℝ} (hc : 0 < c) (hx : 1 < x) : x < endpoint c x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  exact lt_add_of_pos_right _ (mul_pos (mul_pos hc (Real.sqrt_pos.2 hx0)) (Real.log_pos hx))

theorem card_loss {c x : ℝ} (hx : 0 ≤ x) (hxy : x ≤ endpoint c x) :
    halfOpenCount c x ≤ openCount c x + 1 := by
  change piReal (endpoint c x) - piReal x ≤ _
  rw [← halfPrimes_card hxy]
  exact (Finset.card_le_card (halfPrimes_subset_insert hx hxy)).trans (Finset.card_insert_le _ _)

theorem eventual_margin {a c : ℝ} (h : GoodCoefficient a c) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ x : ℝ in atTop, (a+d)*Real.sqrt x ≤ (openCount c x : ℝ) := by
  obtain ⟨hc, d, hd, h⟩ := h
  refine ⟨d/2, by positivity, ?_⟩
  filter_upwards [h, eventually_ge_atTop (2:ℝ),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (2/d)] with x hN hx hlarge
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hm := (le_div_iff₀ (Real.sqrt_pos.2 hx0)).mp hN
  have hl : (halfOpenCount c x : ℝ) ≤ (openCount c x : ℝ) + 1 := by
    exact_mod_cast card_loss hx0.le (endpoint_lt hc hx1).le
  have hlarge' := (div_le_iff₀ hd).mp hlarge
  linarith

theorem eventual_more {a c : ℝ} (h : GoodCoefficient a c) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, a*Real.sqrt x + K < (openCount c x : ℝ) := by
  obtain ⟨d, hd, hd'⟩ := eventual_margin h
  filter_upwards [hd', Real.tendsto_sqrt_atTop.eventually_ge_atTop ((K+1)/d)]
    with x hx hlarge
  have hlarge' := (div_le_iff₀ hd).mp hlarge
  linarith

theorem strict_three (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, a3*Real.sqrt x + K < (openCount 3 x : ℝ) :=
  eventual_more (good_three hNorm hUniform rh) K

theorem strict_five (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, a5*Real.sqrt x + K < (openCount 5 x : ℝ) :=
  eventual_more (good_five hNorm hUniform rh) K


def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem piReal_at_prime (n : ℕ) : piReal (nthPrime n : ℝ) = n+1 := by
  rw [piReal, Nat.floor_natCast, Nat.primeCounting_eq_primeCounting'_succ]
  change Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) = n + 1
  rw [Nat.count_succ, Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime,
    ite_eq_left (Nat.prime_nth_prime n)]

/-- Exact rank test for the general strict-open count at a prime base. -/
theorem prime_rank_iff {y : ℝ} {n k : ℕ} (hy : (nthPrime n : ℝ) < y) (hk : 0 < k) :
    (nthPrime (n+k) : ℝ) < y ↔ k ≤ (openPrimes (nthPrime n : ℝ) y).card := by
  rw [openPrimes_card (Nat.cast_nonneg _) hy, piReal_at_prime]
  have he : nthPrime (n+k) < ⌈y⌉₊ ↔ n+k < Nat.primeCounting' ⌈y⌉₊ := by
    constructor
    · intro h
      have hm := Nat.monotone_primeCounting' (Nat.succ_le_of_lt h)
      rw [← Nat.primeCounting_eq_primeCounting'_succ] at hm
      have hr := piReal_at_prime (n+k)
      rw [piReal, Nat.floor_natCast] at hr
      omega
    · intro h
      by_contra! hn
      have hm := Nat.monotone_primeCounting' hn
      have hr : Nat.primeCounting' (nthPrime (n+k)) = n+k := Nat.primeCounting'_nth_eq _
      omega
  rw [← Nat.lt_ceil, he]
  omega

theorem prime_base_tendsto : Tendsto (fun n => (nthPrime n : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ⌈b⌉₊] with n hn
  apply (Nat.le_ceil b).trans
  exact_mod_cast hn.trans ((Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n))

/-- The rank statement keeps an arbitrary fixed additional rank j. -/
theorem eventual_prime_rank {a c : ℝ} (ha : 0 ≤ a) (h : GoodCoefficient a c) (j : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let x : ℝ := nthPrime n
      let k := ⌊a * Real.sqrt x⌋₊ + 1 + j
      x < (nthPrime (n+k) : ℝ) ∧ (nthPrime (n+k) : ℝ) < endpoint c x := by
  have hb := prime_base_tendsto.eventually (eventual_more h (j : ℝ))
  filter_upwards [hb, prime_base_tendsto.eventually_ge_atTop (2:ℝ)] with n hn hx
  dsimp
  have hx1 : 1 < (nthPrime n : ℝ) := by linarith
  have hy := endpoint_lt h.1 hx1
  have hmul : 0 ≤ a * Real.sqrt (nthPrime n : ℝ) := by positivity
  have hlt : ⌊a * Real.sqrt (nthPrime n : ℝ)⌋₊ + j < openCount c (nthPrime n : ℝ) := by
    exact_mod_cast (show
      ((⌊a * Real.sqrt (nthPrime n : ℝ)⌋₊ : ℕ) : ℝ) + (j : ℝ)
        < (openCount c (nthPrime n : ℝ) : ℝ) from
      (add_le_add (Nat.floor_le hmul) le_rfl).trans_lt hn)
  have hr : 0 < ⌊a * Real.sqrt (nthPrime n : ℝ)⌋₊ + 1 + j := by omega
  refine ⟨?_, (prime_rank_iff hy hr).mpr ?_⟩
  · exact_mod_cast nthPrime_strictMono (Nat.lt_add_of_pos_right hr)
  · change _ ≤ openCount c (nthPrime n : ℝ)
    omega

theorem prime_rank_three (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis) (j : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let x : ℝ := nthPrime n
      let k := ⌊a3 * Real.sqrt x⌋₊ + 1 + j
      x < (nthPrime (n+k) : ℝ) ∧ (nthPrime (n+k) : ℝ) < endpoint 3 x :=
  eventual_prime_rank (by norm_num [a3]) (good_three hNorm hUniform rh) j

theorem prime_rank_five (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis) (j : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let x : ℝ := nthPrime n
      let k := ⌊a5 * Real.sqrt x⌋₊ + 1 + j
      x < (nthPrime (n+k) : ℝ) ∧ (nthPrime (n+k) : ℝ) < endpoint 5 x :=
  eventual_prime_rank (by norm_num [a5]) (good_five hNorm hUniform rh) j


theorem envelope_strictMono : StrictMono envelope := by
  intro a b hab
  have hg : G a < G b := by unfold G q; linarith
  have hs : S a < S b := by unfold S; linarith
  have hf : F a < F b := by unfold F; linarith
  apply lt_min ((min_le_left _ _).trans_lt hg)
  exact lt_min
    (((min_le_right _ _).trans (min_le_left _ _)).trans_lt hs)
    (((min_le_right _ _).trans (min_le_right _ _)).trans_lt hf)

theorem direct_imp_le {a c : ℝ} (h : direct a c) : envelope a ≤ c := by
  rcases h with h | h | h
  · exact (min_le_left _ _).trans h.le
  · exact ((min_le_right _ _).trans (min_le_left _ _)).trans h
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans h

theorem direct_of_lt {a c : ℝ} (h : envelope a < c) : direct a c := by
  rcases lt_or_ge a u with hu|hu
  · exact (direct_left hu).mpr h
  rcases le_or_gt a v with hv|hv
  · exact (direct_middle hu hv).mpr h.le
  · exact (direct_right hv.le).mpr h.le

def gInv (c : ℝ) : ℝ := (c/q-1)/2
def sInv (c : ℝ) : ℝ := (c-944247/1000000)/(1163388/1000000)
def fInv (c : ℝ) : ℝ := (c-9/8)/(16/15)

theorem inverse_left {c : ℝ} (hc : c < U) (a : ℝ) :
    direct a c ↔ a < gInv c := by
  have hb : gInv c < u := by unfold gInv q u U at *; linarith
  have he : envelope (gInv c) = c := by rw [envelope_left hb.le]; unfold G gInv q; ring
  constructor
  · intro h
    have hle := direct_imp_le h
    by_contra! hn
    have h' := envelope_strictMono.monotone hn
    rw [he] at h'
    have ha : a = gInv c := by
      apply envelope_strictMono.injective
      exact (le_antisymm hle h').trans he.symm
    subst a
    exact (lt_irrefl _) (he ▸ (direct_left hb).mp h)
  · intro h
    apply direct_of_lt
    exact (envelope_strictMono h).trans_eq he

theorem inverse_middle {c : ℝ} (h₁ : U ≤ c) (h₂ : c ≤ V) (a : ℝ) :
    direct a c ↔ a ≤ sInv c := by
  have hu : u ≤ sInv c := by unfold sInv U u at *; linarith
  have hv : sInv c ≤ v := by unfold sInv V v at *; linarith
  have he : envelope (sInv c) = c := by rw [envelope_middle hu hv]; unfold S sInv; ring
  constructor
  · intro h
    by_contra! hn
    exact (not_lt_of_ge (direct_imp_le h)) (he ▸ envelope_strictMono hn)
  · intro h
    rcases lt_or_eq_of_le h with h|rfl
    · exact direct_of_lt ((envelope_strictMono h).trans_eq he)
    · exact (direct_middle hu hv).mpr he.le

theorem inverse_right {c : ℝ} (hc : V ≤ c) (a : ℝ) :
    direct a c ↔ a ≤ fInv c := by
  have hv : v ≤ fInv c := by unfold fInv V v at *; linarith
  have he : envelope (fInv c) = c := by rw [envelope_right hv]; unfold F fInv; ring
  constructor
  · intro h
    by_contra! hn
    exact (not_lt_of_ge (direct_imp_le h)) (he ▸ envelope_strictMono hn)
  · intro h
    rcases lt_or_eq_of_le h with h|rfl
    · exact direct_of_lt ((envelope_strictMono h).trans_eq he)
    · exact (direct_right hv).mpr he.le

theorem inverse_empty {a c : ℝ} (ha : 0 ≤ a) (hc : c ≤ q) : ¬ direct a c := by
  have h := (inverse_left (hc.trans_lt widths.2.2.2.2.1) a)
  have hc' : gInv c ≤ 0 := by unfold gInv q at *; linarith
  exact fun hd => (not_lt_of_ge (hc'.trans ha)) (h.mp hd)

/-- Epsilon lower-limit formulation, valid also if the extended-real lower limit is infinite. -/
theorem gaussian_inverse_limit (hCMS : CMSFunctionalInput.v1.population_reduction)
    (rh : RiemannHypothesis) {c : ℝ} (hc : q < c) (e : ℝ) (he : 0 < e) :
    ∀ᶠ x : ℝ in atTop, (gInv c-e)*Real.sqrt x < (openCount c x : ℝ) := by
  have hpos : 0 < gInv c := by unfold gInv q at *; linarith
  have hmax : 0 ≤ max 0 (gInv c-e) := le_max_left _ _
  have hlt : max 0 (gInv c-e) < gInv c := max_lt hpos (sub_lt_self _ he)
  have hg : G (max 0 (gInv c-e)) < c := by
    unfold G gInv q at *
    linarith
  have hgood := ofG hCMS rh hmax hg
  filter_upwards [eventual_more hgood 0] with x hx
  have hle := mul_le_mul_of_nonneg_right (le_max_right 0 (gInv c-e)) (Real.sqrt_nonneg x)
  exact hle.trans_lt (by simpa only [add_zero] using hx)

def oldLead (c : ℝ) : ℝ := (8/9)*c - 18203/20000
def oldWidth (a : ℝ) : ℝ := (9/8)*(a + 18203/20000)

theorem oldWidth_domain (a : ℝ) :
    (103/100 ≤ oldWidth a ∧ oldWidth a ≤ 16) ↔
      (973/180000 ≤ a ∧ a ≤ 2396173/180000) := by
  unfold oldWidth
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem old_inverse (a : ℝ) (c : ℝ) :
    oldLead (oldWidth a) = a ∧ oldWidth (oldLead c) = c := by
  unfold oldWidth oldLead
  constructor <;> ring

theorem old_width_one : oldWidth 1 = 343827/160000 := by norm_num [oldWidth]

theorem octic_gains :
    oldLead 3 = 105391/60000 ∧ oldLead 5 = 636173/180000 ∧
    a3 - oldLead 3 = 61212941/5816940000 ∧ a5 - oldLead 5 = 70933/720000 ∧
    oldWidth a3 - 3 = 183638823/15511840000 ∧ oldWidth a5 - 5 = 70933/640000 ∧
    103/100 ≤ oldWidth a3 ∧ oldWidth a3 ≤ 16 ∧
    103/100 ≤ oldWidth a5 ∧ oldWidth a5 ≤ 16 := by
  norm_num [a3,a5,oldLead,oldWidth]

theorem octic_leading_width_gain (a : ℝ) :
    oldWidth a - envelope a =
      if a < u then 150039188346073/789790351840000 - (2*q-9/8)*a
      else if a ≤ v then 318687/4000000 - (19194/500000)*a
      else (7/120)*a - 16173/160000 := by
  split_ifs with h₁ h₂
  · rw [envelope_left h₁.le]
    unfold oldWidth G q
    ring
  · rw [envelope_middle (le_of_not_gt h₁) h₂]
    unfold oldWidth S
    ring
  · rw [envelope_right (le_of_not_ge h₂)]
    unfold oldWidth F
    ring


/-- A comparison of these specified leading widths, restricted to the
    parameter range of the preserved octic statement. -/
theorem octic_domain_gain (a : ℝ) (_h₁ : 103/100 ≤ oldWidth a) (_h₂ : oldWidth a ≤ 16) :
    0 < oldWidth a - envelope a := by
  rw [octic_leading_width_gain]
  split_ifs with h₁ h₂
  · unfold q u at *
    linarith
  · unfold v at *
    linarith
  · push_neg at h₂
    unfold v at *
    linarith

end
end PopulationTransfer

#print axioms PopulationTransfer.good_three
#print axioms PopulationTransfer.good_five
#print axioms PopulationTransfer.strict_three
#print axioms PopulationTransfer.strict_five
#print axioms PopulationTransfer.prime_rank_three
#print axioms PopulationTransfer.prime_rank_five
#print axioms PopulationTransfer.of_direct
#print axioms PopulationTransfer.infGood_le_envelope
#print axioms PopulationTransfer.inverse_left
#print axioms PopulationTransfer.inverse_middle
#print axioms PopulationTransfer.inverse_right
#print axioms PopulationTransfer.gaussian_inverse_limit
#print axioms PopulationTransfer.octic_gains
#print axioms PopulationTransfer.octic_domain_gain
