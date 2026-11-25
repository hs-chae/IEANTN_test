import Mathlib

namespace CubeStudy
open Real Set Finset Filter
noncomputable section
set_option maxHeartbeats 1000000

def strictPrimes (a b : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊b⌋₊).filter fun p => a < (p : ℝ) ∧ (p : ℝ) < b

def count (a b : ℝ) : ℝ := (strictPrimes a b).card
def weighted (a b : ℝ) : ℝ := ∑ p ∈ strictPrimes a b, log (p : ℝ)
def density (c n : ℝ) : Prop := c * n^2 / log n < count (n^3) ((n+1)^3)

def schErr (x : ℝ) : ℝ := sqrt x * (log x - 2) * log x / (8 * π)

/-- Schoenfeld 1976, Thm 10 (6.1), p.337. Explicit source contract. -/
def Schoenfeld61 : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 2300000000 ≤ x →
    |Chebyshev.theta x - x| < schErr x

/-- Büthe, arXiv:1511.02032v2 Thm 2 (1.6). -/
def Buthe16 : Prop :=
  ∀ x : ℝ, 1423 ≤ x → x ≤ 10^19 → x - Chebyshev.theta x ≤ (39/20) * sqrt x

/-- Büthe, arXiv:1511.02032v2 Thm 2 (1.7). -/
def Buthe17 : Prop :=
  ∀ x : ℝ, 1 ≤ x → x ≤ 10^19 → (1/20) * sqrt x < x - Chebyshev.theta x

lemma mem_strict {a b : ℝ} (hb : 0 ≤ b) (p : ℕ) :
    p ∈ strictPrimes a b ↔ p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) < b := by
  unfold strictPrimes
  simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.le_floor_iff hb]
  constructor
  · rintro ⟨⟨_, hp⟩, ha, hb'⟩
    exact ⟨hp, ha, hb'⟩
  · rintro ⟨hp, ha, hb'⟩
    exact ⟨⟨hb'.le, hp⟩, ha, hb'⟩

def lePrimes (b : ℝ) : Finset ℕ := (Finset.Ioc 0 ⌊b⌋₊).filter Nat.Prime

lemma mem_lePrimes {b : ℝ} (hb : 0 ≤ b) (p : ℕ) :
    p ∈ lePrimes b ↔ p.Prime ∧ (p : ℝ) ≤ b := by
  unfold lePrimes
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.le_floor_iff hb]
  constructor
  · rintro ⟨⟨_, hb'⟩, hp⟩
    exact ⟨hp, hb'⟩
  · rintro ⟨hp, hb'⟩
    exact ⟨⟨hp.pos, hb'⟩, hp⟩

lemma theta_diff {a y b : ℝ} (ha : 0 ≤ a) (hay : a ≤ y) (hyb : y < b)
    (hgap : ∀ p : ℕ, (p : ℝ) < b → (p : ℝ) ≤ y) :
    Chebyshev.theta y - Chebyshev.theta a = weighted a b := by
  have hy := ha.trans hay
  have hb := hy.trans hyb.le
  have hsub : lePrimes a ⊆ lePrimes y := by
    intro p hp
    rw [mem_lePrimes ha] at hp
    rw [mem_lePrimes hy]
    exact ⟨hp.1, hp.2.trans hay⟩
  have he : lePrimes y \ lePrimes a = strictPrimes a b := by
    ext p
    rw [Finset.mem_sdiff, mem_lePrimes hy, mem_lePrimes ha, mem_strict hb]
    constructor
    · rintro ⟨⟨hp, hpy⟩, h⟩
      exact ⟨hp, lt_of_not_ge fun hpa => h ⟨hp,hpa⟩, hpy.trans_lt hyb⟩
    · rintro ⟨hp,hap,hpb⟩
      exact ⟨⟨hp,hgap p hpb⟩,fun hpa => (not_le_of_gt hap) hpa.2⟩
  have hs := Finset.sum_sdiff (f := fun p : ℕ => log (p : ℝ)) hsub
  rw [he] at hs
  change weighted a b + Chebyshev.theta a = Chebyshev.theta y at hs
  linarith

/-- Left limit at the open upper endpoint: no assumption that b is composite. -/
lemma lower_at_open_right {L a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hLb : L < b)
    {f : ℝ → ℝ} (hcont : ContinuousAt f b)
    (hlower : ∀ y ∈ Set.Ioo L b, f y ≤ Chebyshev.theta y) :
    f b - Chebyshev.theta a ≤ weighted a b := by
  let m := ⌈b⌉₊ - 1
  have hb : 0 < b := ha.trans_lt hab
  have hceil : 0 < ⌈b⌉₊ := by
    by_contra! h
    have h' := Nat.le_ceil b
    simp [Nat.eq_zero_of_le_zero h] at h'
    linarith
  have hmcast : (m : ℝ) = (⌈b⌉₊ : ℝ) - 1 := by
    dsimp [m]
    rw [Nat.cast_sub (by omega)]
    simp
  have hmb : (m : ℝ) < b := by
    rw [hmcast]
    have h := Nat.ceil_lt_add_one hb.le
    linarith
  let d := max (max L a) (m : ℝ)
  have hdb : d < b := max_lt (max_lt hLb hab) hmb
  have hc : b ∈ closure (Set.Ioo d b) := by
    rw [closure_Ioo hdb.ne]
    exact ⟨hdb.le, le_rfl⟩
  apply ContinuousWithinAt.closure_le hc (hcont.sub continuousAt_const).continuousWithinAt
    continuousWithinAt_const
  intro y hy
  have hyL : L < y := (le_max_left L a).trans_lt ((le_max_left _ _).trans_lt hy.1)
  have hya : a ≤ y := (le_max_right L a).trans ((le_max_left _ _).trans hy.1.le)
  have hym : (m : ℝ) ≤ y := (le_max_right _ _).trans hy.1.le
  have hg (p : ℕ) (hp : (p : ℝ) < b) : (p : ℝ) ≤ y := by
    have hpc : p < ⌈b⌉₊ := by exact_mod_cast hp.trans_le (Nat.le_ceil b)
    have hpm : p ≤ m := by dsimp [m]; omega
    exact (show (p : ℝ) ≤ m by exact_mod_cast hpm).trans hym
  change f y - Chebyshev.theta a ≤ weighted a b
  rw [← theta_diff ha hya hy.2 hg]
  linarith [hlower y ⟨hyL,hy.2⟩]

lemma weighted_le_count {a b : ℝ} (hb : 0 < b) :
    weighted a b ≤ count a b * log b := by
  unfold weighted count
  rw [← nsmul_eq_mul]
  apply sum_le_card_nsmul
  intro p hp
  have h := (mem_strict hb.le p).mp hp
  exact log_le_log (by exact_mod_cast h.1.pos) h.2.2.le

theorem buthe_raw (hB : Buthe16) (hS : Buthe17) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a < b) (hb0 : 1423 < b) (hb1 : b ≤ 10^19) :
    b - a - (39/20) * sqrt b + (1/20) * sqrt a < count a b * log b := by
  have h := lower_at_open_right (L := 1423) (f := fun x => x-(39/20)*sqrt x)
    (by linarith : 0 ≤ a) hab hb0 (by fun_prop)
    (fun y hy => by linarith [hB y hy.1.le (hy.2.le.trans hb1)])
  have h' := hS a ha (hab.le.trans hb1)
  linarith [weighted_le_count (a := a) (b := b) (by linarith)]

theorem schoenfeld_raw (hS : Schoenfeld61) (rh : RiemannHypothesis) {a b : ℝ}
    (ha : 2300000000 ≤ a) (hab : a < b) :
    b - a - schErr a - schErr b < count a b * log b := by
  have hb : 2300000000 < b := ha.trans_lt hab
  have hc : ContinuousAt (fun x => x-schErr x) b := by
    unfold schErr
    fun_prop (disch := linarith)
  have h := lower_at_open_right (L := 2300000000) (f := fun x => x-schErr x)
    (by linarith : 0 ≤ a) hab hb hc
    (fun y hy => by linarith [(abs_lt.mp (hS rh y hy.1.le)).1])
  linarith [(abs_lt.mp (hS rh a ha)).2,
    weighted_le_count (a := a) (b := b) (by linarith)]

lemma sqrt_cube {n : ℝ} (hn : 0 ≤ n) : sqrt (n^3) = n * sqrt n := by
  rw [show n^3 = n^2*n by ring, sqrt_mul (sq_nonneg _), sqrt_sq hn]

lemma log_step {n : ℝ} (hn : 0 < n) : log (n+1) ≤ log n + 1/n := by
  have hn' : 0 < 1+1/n := by positivity
  have he : n+1 = n*(1+1/n) := by field_simp
  calc
    log (n+1) = log n + log (1+1/n) := by
      rw [he, log_mul hn.ne' hn'.ne']
    _ ≤ _ := by linarith [log_le_sub_one_of_pos hn']

lemma sqrt_step {n : ℝ} (hn : 0 < n) :
    sqrt (n+1) ≤ sqrt n + 1/(2*sqrt n) := by
  have hs : 0 < sqrt n := by positivity
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have he : sqrt n * (1/(2*sqrt n)) = 1/2 := by field_simp
  nlinarith [sq_sqrt hn.le, sq_nonneg (1/(2*sqrt n))]

lemma cube_sqrt_step {n : ℝ} (hn : 1 ≤ n) :
    sqrt ((n+1)^3) ≤ (n+2)*sqrt n := by
  rw [sqrt_cube (by linarith : 0 ≤ n+1)]
  have h := mul_le_mul_of_nonneg_left (sqrt_step (by linarith : 0 < n))
    (by linarith : 0 ≤ n+1)
  have hs : 0 < sqrt n := by positivity
  have haux : (n+1)* (1/(2*sqrt n)) ≤ sqrt n := by
    rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 2*sqrt n)]
    nlinarith [sq_sqrt (by linarith : 0 ≤ n)]
  linarith

lemma density_of_normalized {c n : ℝ} (hn : 1 < n)
    (h : c * (3*n^2) * (log (n+1)/log n) <
      count (n^3) ((n+1)^3) * log ((n+1)^3)) : density c n := by
  unfold density
  rw [log_pow] at h
  have hl := log_pos hn
  have hL : 0 < log (n+1) := log_pos (by linarith)
  refine lt_of_mul_lt_mul_right (c := 3 * log (n+1)) ?_ (by positivity)
  norm_num only [Nat.cast_ofNat] at h
  calc
    _ = c * (3*n^2) * (log (n+1)/log n) := by ring
    _ < _ := h

/-- Uniform in a finite slab: r bounds 1/n, t bounds 1/sqrt(n), and L ≤ log n. -/
theorem buthe_density (hB : Buthe16) (hS : Buthe17) {c n r t L : ℝ}
    (hc : 0 ≤ c) (hn : 11 ≤ n) (hb : (n+1)^3 ≤ 10^19)
    (hr : 1/n ≤ r) (ht : 1/sqrt n ≤ t) (hL : L ≤ log n) (hL0 : 0 < L)
    (hcoef : c * (1 + r/L) ≤ 1 - (19/30)*t) :
    density c n := by
  have hn0 : 0 < n := by linarith
  have hn1 : 1 < n := by linarith
  have hs0 : 0 < sqrt n := by positivity
  have hl : 0 < log n := log_pos hn1
  have ha : (1 : ℝ) ≤ n^3 := one_le_pow₀ hn1.le
  have hab : n^3 < (n+1)^3 := pow_lt_pow_left₀ (by linarith) hn0.le (by norm_num)
  have hb0 : (1423 : ℝ) < (n+1)^3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 12) (show 12 ≤ n+1 by linarith) 3
    linarith
  have h := buthe_raw hB hS ha hab hb0 hb
  rw [sqrt_cube hn0.le] at h
  have hs13 : (13/10 : ℝ) ≤ sqrt n := by
    apply (Real.le_sqrt (by norm_num) hn0.le).mpr
    linarith
  have hs := sq_sqrt hn0.le
  have hp : (3*n^2) * (1 - (19/30)*t) ≤
      (n+1)^3 - n^3 - (39/20)*sqrt ((n+1)^3) + (1/20)*(n*sqrt n) := by
    have he : n^2 * (1/sqrt n) = n*sqrt n := by
      field_simp
      nlinarith [congrArg (fun z : ℝ => n*z) hs]
    have ht' := mul_le_mul_of_nonneg_left ht (sq_nonneg n)
    rw [he] at ht'
    linarith [mul_nonneg (show 0 ≤ sqrt n-13/10 by linarith) hs0.le,
      cube_sqrt_step hn1.le]
  have hmono : log (n+1)/log n ≤ 1 + r/L := by
    have q : (1/n)/log n ≤ r/L := by
      apply (div_le_div_of_nonneg_right hr hl.le).trans
      exact div_le_div_of_nonneg_left ((show (0 : ℝ) ≤ 1/n by positivity).trans hr) hL0 hL
    calc
      _ ≤ (log n+1/n)/log n := div_le_div_of_nonneg_right (log_step hn0) hl.le
      _ = 1 + (1/n)/log n := by rw [add_div, div_self hl.ne']
      _ ≤ _ := by linarith
  apply density_of_normalized hn1
  calc
    _ ≤ (3*n^2)*(c*(1+r/L)) := by
      have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hc)
        (show 0 ≤ 3*n^2 by positivity)
      linarith
    _ ≤ _ := (mul_le_mul_of_nonneg_left hcoef (by positivity : 0 ≤ 3*n^2)).trans hp
    _ < _ := h


/-- Quadratic times exp(-x/2) decreases after x=5. Proof uses only Taylor
terms of the exponential with nonnegative argument, no floating samples. -/
lemma sch_quad_decay {l z d : ℝ} (hz : 5 ≤ z) (hl : z ≤ l) (hd : 0 ≤ d) :
    l*(3*l-2+d) ≤ z*(3*z-2+d) * exp ((l-z)/2) := by
  let v := l-z
  let P := z*(3*z-2+d)
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have hP : 0 ≤ P := by dsimp [P]; exact mul_nonneg (by linarith) (by linarith)
  have h1 : 6*z-2+d ≤ P/2 := by
    dsimp [P]
    nlinarith [sq_nonneg (z-5), mul_nonneg hd (show 0 ≤ z-2 by linarith)]
  have h2 : 3 ≤ P/8 := by
    dsimp [P]
    nlinarith [sq_nonneg (z-5), mul_nonneg hd (show 0 ≤ z by linarith)]
  have hev := Real.sum_le_exp_of_nonneg (show 0 ≤ v/2 by positivity) 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at hev
  calc
    _ = P + (6*z-2+d)*v + 3*v^2 := by dsimp [P,v]; ring
    _ ≤ P*(1+v/2+v^2/8) := by
      nlinarith only [mul_le_mul_of_nonneg_right h1 hv, mul_le_mul_of_nonneg_right h2 (sq_nonneg v)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hP
      linarith

theorem schoenfeld_density (hS : Schoenfeld61) (rh : RiemannHypothesis)
    {c n n₀ r L T : ℝ} (hn : n₀ ≤ n) (hn₀ : 1 < n₀)
    (ha₀ : 2300000000 ≤ n₀^3) (hr : 1/n₀ ≤ r)
    (hl₀ : 5 ≤ log n₀) (hL : log n₀ ≤ L) (hT : T ≤ sqrt n₀) (hc : c ≤ 1)
    (hcoef : (2+2*r)*(L*(3*L-2+3*r)) ≤ (1-c)*8*π*T) :
    density c n := by
  have hn1 : 1 < n := hn₀.trans_le hn
  have hn0 := zero_lt_one.trans hn1
  have hlog := log_le_log (zero_lt_one.trans hn₀) hn
  have hl5 : 5 ≤ log n := hl₀.trans hlog
  have hr0 : 0 ≤ r := (by positivity : 0 ≤ 1/n₀).trans hr
  have hrec : 1/n ≤ r := (one_div_le_one_div_of_le (by linarith) hn).trans hr
  have hab : n^3 < (n+1)^3 := pow_lt_pow_left₀ (by linarith) hn0.le (by norm_num)
  have ha := ha₀.trans (pow_le_pow_left₀ (by linarith) hn 3)
  have h := schoenfeld_raw hS rh ha hab
  have hla : log (n^3) = 3*log n := by rw [log_pow]; norm_num
  have hlb : log ((n+1)^3) = 3*log (n+1) := by rw [log_pow]; norm_num
  have hlogn : 0 < log n := by linarith
  have hlogstep := log_step hn0
  have hlogmono : log n ≤ log (n+1) := log_le_log hn0 (by linarith)
  have hlogs0 : 0 < log (n+1) := hlogn.trans_le hlogmono
  have herr1 : schErr (n^3) ≤ (n*sqrt n)*(3*log (n+1))*(3*log n-2+3*r)/(8*π) := by
    rw [schErr, sqrt_cube hn0.le, hla]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul (show 3*log n-2 ≤ 3*log n-2+3*r by linarith)
      (show 3*log n ≤ 3*log (n+1) by linarith) (by positivity)
      (show 0 ≤ 3*log n-2+3*r by linarith)
    nlinarith only [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ n*sqrt n)]
  have hs2 : sqrt ((n+1)^3) ≤ (n*sqrt n)*(1+2*r) := by
    have hv : 1 ≤ n*r := by nlinarith [(div_le_iff₀ hn0).mp hrec]
    have hh := mul_le_mul_of_nonneg_right hv (sqrt_nonneg n)
    exact (cube_sqrt_step hn1.le).trans (by nlinarith only [hh])
  have herr2 : schErr ((n+1)^3) ≤
      (n*sqrt n)*(3*log (n+1))*(3*log n-2+3*r)*(1+2*r)/(8*π) := by
    rw [schErr, hlb]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul hs2
      (show 3*log (n+1)-2 ≤ 3*log n-2+3*r by linarith)
      (show 0 ≤ 3*log (n+1)-2 by linarith) (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hh (show 0 ≤ 3*log (n+1) by positivity)]
  let Q := fun l : ℝ => l*(3*l-2+3*r)
  have hd : sqrt n = sqrt n₀ * exp ((log n-log n₀)/2) := by
    rw [← exp_log hn0, ← exp_log (show 0 < n₀ by linarith), ← exp_half, ← exp_half,
      log_exp, log_exp, ← exp_add]
    congr 1
    ring
  have hQ := sch_quad_decay hl₀ hlog (show 0 ≤ 3*r by positivity)
  change Q (log n) ≤ Q (log n₀) * exp ((log n-log n₀)/2) at hQ
  have hQL : Q (log n₀) ≤ Q L := by
    dsimp [Q]
    exact mul_le_mul hL (by linarith) (by linarith) (by linarith)
  have hK : (2+2*r)*Q (log n) ≤ (1-c)*8*π*sqrt n := by
    rw [hd]
    have hg : 0 ≤ 2+2*r := by positivity
    calc
      _ ≤ (2+2*r)*(Q L * exp ((log n-log n₀)/2)) :=
        mul_le_mul_of_nonneg_left (hQ.trans (mul_le_mul_of_nonneg_right hQL (exp_nonneg _))) hg
      _ = ((2+2*r)*Q L) * exp ((log n-log n₀)/2) := by ring
      _ ≤ ((1-c)*8*π*sqrt n₀) * exp ((log n-log n₀)/2) := by
        apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
        exact hcoef.trans (mul_le_mul_of_nonneg_left hT (by positivity))
      _ = _ := by ring
  have hgeom : (3*n^2)*(log (n+1)/log n) ≤ (n+1)^3 - n^3 := by
    rw [← mul_div_assoc, div_le_iff₀ hlogn]
    have he : n^2*(1/n) = n := by field_simp
    have hv := mul_le_mul_of_nonneg_left hlogstep (show 0 ≤ 3*n^2 by positivity)
    have ht := mul_nonneg (show 0 ≤ 3*log n-3 by linarith) hn0.le
    nlinarith [he, mul_nonneg hlogn.le (show 0 ≤ 1 by norm_num)]
  have herr : schErr (n^3)+schErr ((n+1)^3) ≤
      (1-c)*(3*n^2)*(log (n+1)/log n) := by
    have hf : 0 < 8*π := by positivity
    have hfac : 0 < (n*sqrt n)*(3*log (n+1)) := by positivity
    have hh : ((2+2*r)*(3*log n-2+3*r))/(8*π) ≤ (1-c)*sqrt n/log n := by
      rw [div_le_div_iff₀ hf hlogn]
      dsimp [Q] at hK
      nlinarith only [hK]
    calc
      _ ≤ (n*sqrt n)*(3*log (n+1))*(((2+2*r)*(3*log n-2+3*r))/(8*π)) := by
        linarith only [herr1, herr2, show
          (n*sqrt n)*(3*log (n+1))*(((2+2*r)*(3*log n-2+3*r))/(8*π)) =
          (n*sqrt n)*(3*log (n+1))*(3*log n-2+3*r)/(8*π)+
          (n*sqrt n)*(3*log (n+1))*(3*log n-2+3*r)*(1+2*r)/(8*π) from by ring]
      _ ≤ (n*sqrt n)*(3*log (n+1))*((1-c)*sqrt n/log n) :=
        mul_le_mul_of_nonneg_left hh hfac.le
      _ = _ := by
        field_simp
        ring_nf
        rw [sq_sqrt hn0.le]
        ring
  apply density_of_normalized hn1
  linarith only [h, hgeom, herr, show
    c*(3*n^2)*(log (n+1)/log n) = (3*n^2)*(log (n+1)/log n) -
      (1-c)*(3*n^2)*(log (n+1)/log n) from by ring]


lemma log_lower_small_int (k : ℕ) {n : ℝ} (hn : 0 < n)
    (hb : (2719/1000 : ℝ)^k ≤ n) : (k : ℝ) ≤ log n := by
  apply (Real.le_log_iff_exp_le hn).mpr
  rw [show (k : ℝ) = k*(1 : ℝ) by ring, exp_nat_mul]
  exact (pow_le_pow_left₀ (exp_nonneg _) (by linarith [Real.exp_one_lt_d9]) k).trans hb

lemma exp8_gt_2980 : (2980 : ℝ) < exp 8 := by
  have h := pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9] :
    (271828/100000 : ℝ) < exp 1) (by norm_num) (show (8 : ℕ) ≠ 0 by norm_num)
  rw [← exp_nat_mul] at h
  norm_num at h
  linarith


lemma exp_nat_lower (k : ℕ) : (2718281828/1000000000 : ℝ)^k ≤ exp (k : ℝ) := by
  rw [show (k : ℝ) = k*(1 : ℝ) by ring, exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) k

lemma log_cutoff_upper : log (2154000 : ℝ) ≤ 14583/1000 := by
  apply (log_le_iff_le_exp (by norm_num)).mpr
  rw [show (14583/1000 : ℝ) = 14+583/1000 by norm_num, exp_add]
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 583/1000) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hh := exp_nat_lower 14
  norm_num at hh
  have hh' := mul_le_mul hh h (by norm_num) (exp_nonneg _)
  linarith

lemma log_1321_upper : log (1321 : ℝ) ≤ 7187/1000 := by
  apply (log_le_iff_le_exp (by norm_num)).mpr
  rw [show (7187/1000 : ℝ) = 7+187/1000 by norm_num, exp_add]
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 187/1000) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hh := exp_nat_lower 7
  norm_num at hh
  have hh' := mul_le_mul hh h (by norm_num) (exp_nonneg _)
  linarith

lemma cutoff_cover {n : ℝ} (hn : 0 ≤ n) (h : n ≤ 2154000) :
    (n+1)^3 ≤ 10^19 := by
  have hh := pow_le_pow_left₀ (by linarith : 0 ≤ n+1) (show n+1 ≤ 2154001 by linarith) 3
  linarith

theorem schoenfeld_9669 (hS : Schoenfeld61) (rh : RiemannHypothesis)
    {n : ℝ} (hn : 2154000 ≤ n) : density (9669/10000) n := by
  apply schoenfeld_density hS rh (r := 1/2154000) (L := 14583/1000) (T := 1467) hn
  · norm_num
  · norm_num
  · rfl
  · exact_mod_cast log_lower_small_int 5 (n := 2154000) (by norm_num) (by norm_num)
  · exact log_cutoff_upper
  · apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr; norm_num
  · norm_num
  · have hπ : (31415/10000 : ℝ) ≤ π := by linarith [Real.pi_gt_d4]
    norm_num
    linarith

theorem schoenfeld_690 (hS : Schoenfeld61) (rh : RiemannHypothesis)
    {n : ℝ} (hn : 1321 ≤ n) : density (69/100) n := by
  apply schoenfeld_density hS rh (r := 1/1321) (L := 7187/1000) (T := 3634/100) hn
  · norm_num
  · norm_num
  · rfl
  · exact_mod_cast log_lower_small_int 5 (n := 1321) (by norm_num) (by norm_num)
  · exact log_1321_upper
  · apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr; norm_num
  · norm_num
  · have hπ : (31415/10000 : ℝ) ≤ π := by linarith [Real.pi_gt_d4]
    norm_num
    linarith

theorem schoenfeld_743 (hS : Schoenfeld61) (rh : RiemannHypothesis)
    {n : ℝ} (hn : exp 8 ≤ n) : density (743/1000) n := by
  apply schoenfeld_density hS rh (r := 1/2980) (L := 8) (T := 5458/100)
      (exp8_gt_2980.le.trans hn)
  · norm_num
  · norm_num
  · rfl
  · exact_mod_cast log_lower_small_int 5 (n := 2980) (by norm_num) (by norm_num)
  · exact (log_le_iff_le_exp (by norm_num)).mpr exp8_gt_2980.le
  · apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr; norm_num
  · norm_num
  · have hπ : (31415/10000 : ℝ) ≤ π := by linarith [Real.pi_gt_d4]
    norm_num
    linarith

theorem hybrid_9669 (hB : Buthe16) (hP : Buthe17) (hS : Schoenfeld61)
    (rh : RiemannHypothesis) {n : ℝ} (hn : 400 ≤ n) : density (9669/10000) n := by
  by_cases hh : n ≤ 2154000
  · have hs : (20 : ℝ) ≤ sqrt n := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
    apply buthe_density hB hP (r := 1/400) (t := 1/20) (L := 5) (by norm_num)
        (by linarith) (cutoff_cover (by linarith) hh)
    · exact one_div_le_one_div_of_le (by norm_num) hn
    · exact one_div_le_one_div_of_le (by norm_num) hs
    · apply (show (5 : ℝ) ≤ log 400 by
        exact_mod_cast log_lower_small_int 5 (n := 400) (by norm_num) (by norm_num)).trans
      exact log_le_log (by norm_num) hn
    · norm_num
    · norm_num
  · exact schoenfeld_9669 hS rh (by linarith)

theorem buthe_988 (hB : Buthe16) (hP : Buthe17)
    {n : ℝ} (hn : exp 8 ≤ n) (hb : n ≤ 2154000) : density (988/1000) n := by
  have hn' := exp8_gt_2980.le.trans hn
  have hs : (5458/100 : ℝ) ≤ sqrt n := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  apply buthe_density hB hP (r := 1/2980) (t := 100/5458) (L := 8) (by norm_num)
      (by linarith) (cutoff_cover (by linarith) hb)
  · exact one_div_le_one_div_of_le (by norm_num) hn'
  · simpa only [show (1:ℝ)/(5458/100)=100/5458 by norm_num] using
      one_div_le_one_div_of_le (by norm_num) hs
  · exact (Real.le_log_iff_exp_le (by linarith)).mpr hn
  · norm_num
  · norm_num

#print axioms lower_at_open_right
#print axioms buthe_raw
#print axioms schoenfeld_raw
#print axioms buthe_density
#print axioms schoenfeld_density
#print axioms schoenfeld_690
#print axioms schoenfeld_743
#print axioms schoenfeld_9669
#print axioms hybrid_9669
#print axioms buthe_988
end
end CubeStudy
