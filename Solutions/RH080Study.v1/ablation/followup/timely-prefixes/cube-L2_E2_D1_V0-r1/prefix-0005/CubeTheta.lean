
import QuarticWindow
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.ExponentialBounds
import CompactDualVerified

/-! Source-conditional strict-open Chebyshev consumers. Neither source formula
is postulated as an axiom: both are explicit inputs to the final theorems. -/
noncomputable section
open Real Set Filter
open scoped Topology
namespace CubeTheta

def count (a b : ℝ) : ℝ := (QuarticWindow.primesBetween a b).card

def err (x : ℝ) : ℝ := sqrt x * (log x - 2) * log x / (8 * π)

def Schoenfeld61 : Prop := RiemannHypothesis →
  ∀ x : ℝ, 2300000000 ≤ x → |Chebyshev.theta x - x| < err x

def Buthe1617 : Prop :=
  (∀ x : ℝ, 1423 ≤ x → x ≤ 10^19 → x - Chebyshev.theta x ≤ (195/100 : ℝ) * sqrt x) ∧
  (∀ x : ℝ, 1 ≤ x → x ≤ 10^19 → (5/100 : ℝ) * sqrt x < x - Chebyshev.theta x)

#check RH080.Dual.kernel_compact_obstruction

lemma mem_primes {x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ Nat.primesLE ⌊x⌋₊ ↔ p.Prime ∧ (p : ℝ) ≤ x := by
  rw [Nat.mem_primesLE]
  constructor
  · rintro ⟨h, hp⟩
    exact ⟨hp, (Nat.cast_le.mpr h).trans (Nat.floor_le hx)⟩
  · rintro ⟨hp, h⟩
    exact ⟨Nat.le_floor h, hp⟩

lemma theta_le_open {a z b : ℝ} (ha : 0 ≤ a) (haz : a < z) (hzb : z < b) :
    Chebyshev.theta z ≤ Chebyshev.theta a + count a b * log b := by
  classical
  have hz := ha.trans haz.le
  have hb := hz.trans hzb.le
  let A := Nat.primesLE ⌊a⌋₊
  let Z := Nat.primesLE ⌊z⌋₊
  have hAZ : A ⊆ Z := by
    intro p hp
    exact (mem_primes hz).mpr ⟨((mem_primes ha).mp hp).1, ((mem_primes ha).mp hp).2.trans haz.le⟩
  have hsub : Z \ A ⊆ QuarticWindow.primesBetween a b := by
    intro p hp
    obtain ⟨hpZ, hpA⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpp, hpz⟩ := (mem_primes hz).mp hpZ
    exact Finset.mem_filter.mpr ⟨(mem_primes hb).mpr ⟨hpp, hpz.trans hzb.le⟩,
      lt_of_not_ge (fun h => hpA ((mem_primes ha).mpr ⟨hpp, h⟩)), hpz.trans_lt hzb⟩
  have hv := Finset.sum_sdiff (f := fun p : ℕ => log (p : ℝ)) hAZ
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => log (p : ℝ)) hsub
    (fun p hp _ => log_nonneg (by
      have h := ((mem_primes hb).mp (Finset.mem_filter.mp hp).1).1.one_lt
      exact_mod_cast h.le))
  have hc := Finset.sum_le_card_nsmul (f := fun p : ℕ => log (p : ℝ)) (QuarticWindow.primesBetween a b) (log b)
    (fun p hp => log_le_log (by
      have h := ((mem_primes hb).mp (Finset.mem_filter.mp hp).1).1.pos
      exact_mod_cast h) (Finset.mem_filter.mp hp).2.2.le)
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
  dsimp [count]
  rw [nsmul_eq_mul] at hc
  change ∑ p ∈ Z, log (p : ℝ) ≤ ∑ p ∈ A, log (p : ℝ) + _
  linarith

/-- Take the lower envelope at b from BELOW; one does not discard a unit
or assume b is composite. Strictness can come from the upper bound at a. -/
lemma endpoint_transfer {a b U : ℝ} {f : ℝ → ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hcont : ContinuousAt f b) (hlower : ∀ z ∈ Ioo a b, f z ≤ Chebyshev.theta z)
    (hupper : Chebyshev.theta a < U) :
    f b - U < count a b * log b := by
  have ht : Tendsto f (𝓝[<] b) (𝓝 (f b)) := hcont.continuousWithinAt
  have hv : f b ≤ Chebyshev.theta a + count a b * log b := by
    apply le_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsLT hab] with z hz
    exact (hlower z hz).trans (theta_le_open ha hz.1 hz.2)
  linarith

lemma buthe_raw (hB : Buthe1617) {n : ℝ} (hn : (45/4 : ℝ) ≤ n)
    (hcap : (n+1)^3 ≤ 10^19) :
    (n+1)^3 - n^3 + (5/100 : ℝ) * sqrt (n^3) - (195/100 : ℝ) * sqrt ((n+1)^3)
      < count (n^3) ((n+1)^3) * log ((n+1)^3) := by
  have hn0 : 0 < n := by linarith
  have ha : (1423 : ℝ) ≤ n^3 := (show (1423 : ℝ) ≤ (45/4 : ℝ)^3 by norm_num).trans
    (pow_le_pow_left₀ (by norm_num) hn 3)
  have hab : n^3 < (n+1)^3 := pow_lt_pow_left₀ (by linarith) hn0.le (by norm_num)
  have hu := hB.2 (n^3) (by linarith) (hab.le.trans hcap)
  have ht := endpoint_transfer (f := fun x => x - (195/100 : ℝ) * sqrt x)
    (U := n^3 - (5/100 : ℝ) * sqrt (n^3)) (pow_nonneg hn0.le 3) hab
    (by fun_prop) (fun z hz => by linarith [hB.1 z (ha.trans hz.1.le) (hz.2.le.trans hcap)])
    (by linarith)
  linarith

lemma schoenfeld_raw (hS : Schoenfeld61) (rh : RiemannHypothesis) {n : ℝ}
    (hn : (2300000000 : ℝ) ≤ n^3) (hn0 : 0 < n) :
    (n+1)^3 - n^3 - err (n^3) - err ((n+1)^3)
      < count (n^3) ((n+1)^3) * log ((n+1)^3) := by
  have hab : n^3 < (n+1)^3 := pow_lt_pow_left₀ (by linarith) hn0.le (by norm_num)
  have hu := (abs_lt.mp (hS rh (n^3) hn)).2
  have hc : ContinuousAt (fun x => x - err x) ((n+1)^3) := by
    have hne : (n+1)^3 ≠ 0 := by positivity
    unfold err
    fun_prop
  have ht := endpoint_transfer (f := fun x => x - err x)
    (U := n^3 + err (n^3)) (pow_nonneg hn0.le 3) hab hc
    (fun z hz => by linarith [(abs_lt.mp (hS rh z (hn.trans hz.1.le))).1])
    (by linarith)
  linarith

lemma sqrt_cube {n : ℝ} (hn : 0 ≤ n) : sqrt (n^3) = n * sqrt n := by
  rw [show n^3 = n^2 * n by ring, sqrt_mul (sq_nonneg _), sqrt_sq hn]

lemma log_step {n : ℝ} (hn : 0 < n) : log (n+1) ≤ log n + 1/n := by
  have h := log_le_sub_one_of_pos (show 0 < (n+1)/n by positivity)
  rw [log_div (by positivity) hn.ne'] at h
  rw [show (n+1)/n - 1 = 1/n by field_simp <;> ring] at h
  linarith

lemma log_ge_two {n : ℝ} (hn : (45/4 : ℝ) ≤ n) : 2 ≤ log n := by
  have h : exp (2 : ℝ) ≤ 9 := by
    rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, exp_nat_mul]
    have hh := pow_le_pow_left₀ (exp_nonneg _) exp_one_lt_three.le 2
    norm_num at hh ⊢
    exact hh
  exact (le_log_iff_exp_le (by linarith)).mpr (h.trans (by linarith))

lemma scaled_target {n c : ℝ} (hn : (45/4 : ℝ) ≤ n) (hc : 0 ≤ c) :
    (c * n^2/log n) * log ((n+1)^3) ≤ 3*c*n^2 + (3/2)*c*n := by
  have hn0 : 0 < n := by linarith
  have hl := log_ge_two hn
  have hl0 : 0 < log n := by linarith
  have hp := mul_le_mul_of_nonneg_left (log_step hn0)
    (show 0 ≤ 3*c*n^2/log n by positivity)
  have he : 3*c*n^2/log n * (log n + 1/n) = 3*c*n^2 + 3*c*n/log n := by
    field_simp
    <;> ring
  rw [he] at hp
  have h₂ : 3*c*n/log n ≤ (3/2)*c*n := (div_le_iff₀ hl0).mpr (by
    nlinarith [mul_nonneg (mul_nonneg hc hn0.le) (show 0 ≤ log n-2 by linarith)])
  rw [log_pow]
  push_cast
  rw [show c*n^2/log n*(3*log (n+1)) = 3*c*n^2/log n*log (n+1) by ring]
  linarith

lemma buthe_density (hB : Buthe1617) {n c : ℝ} (hn : (45/4 : ℝ) ≤ n)
    (hcap : (n+1)^3 ≤ 10^19) (hc : 0 ≤ c)
    (hc' : c ≤ 1 - (19/30 : ℝ) / sqrt n) :
    c * n^2/log n < count (n^3) ((n+1)^3) := by
  have hn0 : 0 < n := by linarith
  have hs : 0 < sqrt n := sqrt_pos.mpr hn0
  have hs2 := sq_sqrt hn0.le
  have hs3 : (3 : ℝ) ≤ sqrt n := (le_sqrt (by norm_num) hn0.le).mpr (by linarith)
  have hc1 : c ≤ 1 := by linarith [div_nonneg (show 0 ≤ (19/30 : ℝ) by norm_num) hs.le]
  have hr := buthe_raw hB hn hcap
  rw [sqrt_cube hn0.le, sqrt_cube (show 0 ≤ n+1 by linarith)] at hr
  have hsnext : (n+1)*sqrt (n+1) ≤ (n+2)*sqrt n := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, mul_pow, sq_sqrt hn0.le, sq_sqrt (show 0 ≤ n+1 by linarith)]
    nlinarith [sq_nonneg n]
  have hcn : 3*c*n^2 ≤ 3*n^2 - (19/10 : ℝ)*n*sqrt n := by
    have hh := mul_le_mul_of_nonneg_right hc' (sq_nonneg n)
    have he : (19/30 : ℝ) / sqrt n * n^2 = (19/30 : ℝ)*n*sqrt n := by
      have h := (div_mul_cancel₀ (19/30 : ℝ) hs.ne')
      calc
        19/30 / sqrt n * n^2 = (19/30 / sqrt n * sqrt n) * n * sqrt n := by linear_combination (19/30 / sqrt n * n) * (-hs2)
        _ = _ := by rw [h]
    rw [sub_mul, one_mul, he] at hh
    linarith
  have hcn' := mul_le_mul_of_nonneg_right hc1 hn0.le
  have hgain : (39/10 : ℝ)*sqrt n ≤ (3/2)*n := by
    nlinarith [mul_nonneg hs.le (show 0 ≤ sqrt n - 3 by linarith)]
  have ht := scaled_target hn hc
  have hl : 0 < log ((n+1)^3) := log_pos (by
    have hn1 : 1 < n+1 := by linarith
    exact one_lt_pow₀ hn1 (by norm_num))
  apply (lt_of_mul_lt_mul_right _ hl.le)
  linarith [show (n+1)^3-n^3=3*n^2+3*n+1 by ring]

def P (t : ℝ) : ℝ := (3*t-2)*t

lemma schoenfeld_err_scale {n m T q : ℝ} (hm : (45/4 : ℝ) ≤ m)
    (hn : m ≤ n) (hT : 7 ≤ T) (hmT : log m ≤ T) (hq : 0 ≤ q)
    (hq' : 3*P T ≤ 8*π*q*sqrt m) : err (n^3) ≤ q*n^2 := by
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := hm0.trans_le hn
  have hmS : 0 < sqrt m := sqrt_pos.mpr hm0
  have hnS : 0 < sqrt n := sqrt_pos.mpr hn0
  let v := log n - log m
  have hv : 0 ≤ v := sub_nonneg.mpr (log_le_log hm0 hn)
  have hl : 2 ≤ log n := log_ge_two (hm.trans hn)
  have hlog : log n ≤ T+v := by dsimp [v]; linarith
  have hlog' : P (log n) ≤ P (T+v) := by
    unfold P
    exact (mul_le_mul
      (show 3*log n-2 ≤ 3*(T+v)-2 by linarith)
      hlog (by linarith) (by linarith))
  have hP0 : 0 ≤ P T := by unfold P; exact mul_nonneg (by linarith) (by linarith)
  have hp1 : 6*T-2 ≤ P T/2 := by
    unfold P
    nlinarith [sq_nonneg (T-7)]
  have hp2 : (3 : ℝ) ≤ P T/8 := by
    unfold P
    nlinarith [sq_nonneg (T-7)]
  have hpoly : P (T+v) ≤ P T * (1+v/2+v^2/8) := by
    unfold P at *
    nlinarith only [mul_le_mul_of_nonneg_right hp1 hv, mul_le_mul_of_nonneg_right hp2 (sq_nonneg v)]
  have hsum := sum_le_exp_of_nonneg (show 0 ≤ v/2 by positivity) 3
  have hev : 1+v/2+v^2/8 ≤ exp (v/2) := by
    norm_num [Finset.sum_range_succ] at hsum
    convert hsum using 1 <;> ring
  have hs : sqrt n = sqrt m * exp (v/2) := by
    rw [sqrt_eq_rpow, sqrt_eq_rpow, rpow_def_of_pos hn0, rpow_def_of_pos hm0, ← exp_add]
    congr 1
    dsimp [v]
    ring
  have hh : 3*P (log n) ≤ (8*π*q)*sqrt n := by
    calc
      3*P (log n) ≤ 3*(P T * exp (v/2)) :=
        mul_le_mul_of_nonneg_left (hlog'.trans (hpoly.trans (mul_le_mul_of_nonneg_left hev hP0))) (by norm_num)
      _ = (3*P T)*exp (v/2) := by ring
      _ ≤ (8*π*q*sqrt m)*exp (v/2) := mul_le_mul_of_nonneg_right hq' (exp_nonneg _)
      _ = (8*π*q)*sqrt n := by rw [hs]; ring
  unfold err
  rw [sqrt_cube hn0.le, log_pow]
  apply (div_le_iff₀ (show 0 < 8*π by positivity)).mpr
  have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ n*sqrt n by positivity)
  push_cast
  calc
    n * sqrt n * (3 * log n - 2) * (3 * log n) = n * sqrt n * (3 * P (log n)) := by unfold P; ring
    _ ≤ n * sqrt n * (8 * π * q * sqrt n) := hh'
    _ = q*n^2*(8*π) := by
      have he : n * sqrt n * sqrt n = n^2 := by rw [mul_assoc, ← sq, sq_sqrt hn0.le]; ring
      linear_combination (8*π*q)*he

lemma schoenfeld_density (hS : Schoenfeld61) (rh : RiemannHypothesis)
    {n m T q c : ℝ} (hm : (45/4 : ℝ) ≤ m) (hmd : (2300000000 : ℝ) ≤ m^3)
    (hn : m ≤ n) (hT : 7 ≤ T) (hmT : log m ≤ T) (hq : 0 ≤ q)
    (hq' : 3*P T ≤ 8*π*q*sqrt m) (hq4 : q ≤ 3/4)
    (hc : 0 ≤ c) (hc' : c ≤ 1-2*q/3) :
    c*n^2/log n < count (n^3) ((n+1)^3) := by
  have hne : (45/4 : ℝ) ≤ n := hm.trans hn
  have hn0 : 0 < n := by linarith
  have hcap : (2300000000 : ℝ) ≤ n^3 := hmd.trans (pow_le_pow_left₀ (by linarith) hn 3)
  have h₁ := schoenfeld_err_scale hm hn hT hmT hq hq'
  have h₂ := schoenfeld_err_scale hm (hn.trans (show n ≤ n+1 by linarith)) hT hmT hq hq'
  have hr := schoenfeld_raw hS rh hcap hn0
  have ht := scaled_target hne hc
  have hcn := mul_le_mul_of_nonneg_right hc' (sq_nonneg n)
  have hc1 : c ≤ 1 := by linarith
  have hmid : (3/2)*c*n ≤ (3-2*q)*n := mul_le_mul_of_nonneg_right (by linarith) hn0.le
  have hlast : 0 ≤ 1-q := by linarith
  have hl : 0 < log ((n+1)^3) := log_pos (by
    have hn1 : 1 < n+1 := by linarith
    exact one_lt_pow₀ hn1 (by norm_num))
  apply (lt_of_mul_lt_mul_right _ hl.le)
  linarith only [ht, hr, h₁, h₂, hcn, hmid, hlast,
    show (n+1)^3-n^3=3*n^2+3*n+1 by ring,
    show q*((n+1)^2)=q*n^2+2*q*n+q by ring]


/-- Family on an exponential ray; supplies only the numeric q certificate. -/
lemma schoenfeld_exp_ray (hS : Schoenfeld61) (rh : RiemannHypothesis)
    {t n q c : ℝ} (ht : 8 ≤ t) (hn : exp t ≤ n)
    (hq : 0 ≤ q) (hq' : 3*P t ≤ 8*π*q*exp (t/2)) (hq4 : q ≤ 3/4)
    (hc : 0 ≤ c) (hc' : c ≤ 1-2*q/3) :
    c*n^2/log n < count (n^3) ((n+1)^3) := by
  have he8 : (2980 : ℝ) ≤ exp 8 := by
    rw [show (8 : ℝ) = (8 : ℕ) * 1 by norm_num, exp_nat_mul]
    have hh := pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 8
    norm_num at hh ⊢
    linarith
  have he := he8.trans (exp_le_exp.mpr ht)
  apply schoenfeld_density hS rh (m := exp t) (T := t) (q := q)
    (by linarith) (by
      have hh := pow_le_pow_left₀ (by norm_num) he 3
      norm_num at hh
      linarith)
    hn (by linarith) (by simp) hq
  · simpa only [← exp_half] using hq'
  · exact hq4
  · exact hc
  · exact hc'

private lemma exp_integer_floor (k : ℕ) : (2.7182818283 : ℝ)^k ≤ exp (k : ℝ) := by
  rw [← mul_one (k : ℝ), exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le _

theorem cube_schoenfeld_exp8 {n : ℝ} (hS : Schoenfeld61) (rh : RiemannHypothesis) (hn : exp 8 ≤ n) :
    (0.74347 : ℝ)*n^2/log n < count (n^3) ((n+1)^3) := by
  apply schoenfeld_exp_ray hS rh (q := 0.384795) (by norm_num) hn (by norm_num) ?_
    (by norm_num) (by norm_num) (by norm_num)
  have hh := mul_le_mul pi_gt_d6.le (exp_integer_floor 4) (by positivity) pi_pos.le
  norm_num [P] at hh ⊢
  linarith

theorem cube_schoenfeld_exp16 {n : ℝ} (hS : Schoenfeld61) (rh : RiemannHypothesis) (hn : exp 16 ≤ n) :
    (0.98 : ℝ)*n^2/log n < count (n^3) ((n+1)^3) := by
  apply schoenfeld_exp_ray hS rh (q := 0.03) (by norm_num) hn (by norm_num) ?_
    (by norm_num) (by norm_num) (by norm_num)
  have hh := mul_le_mul pi_gt_d6.le (exp_integer_floor 8) (by positivity) pi_pos.le
  norm_num [P] at hh ⊢
  linarith

theorem cube_schoenfeld_exp18 {n : ℝ} (hS : Schoenfeld61) (rh : RiemannHypothesis) (hn : exp 18 ≤ n) :
    (0.99 : ℝ)*n^2/log n < count (n^3) ((n+1)^3) := by
  apply schoenfeld_exp_ray hS rh (q := 0.015) (by norm_num) hn (by norm_num) ?_
    (by norm_num) (by norm_num) (by norm_num)
  have hh := mul_le_mul pi_gt_d6.le (exp_integer_floor 9) (by positivity) pi_pos.le
  norm_num [P] at hh ⊢
  linarith

theorem cube_schoenfeld_exp24 {n : ℝ} (hS : Schoenfeld61) (rh : RiemannHypothesis) (hn : exp 24 ≤ n) :
    (0.999 : ℝ)*n^2/log n < count (n^3) ((n+1)^3) := by
  apply schoenfeld_exp_ray hS rh (q := 0.0015) (by norm_num) hn (by norm_num) ?_
    (by norm_num) (by norm_num) (by norm_num)
  have hh := mul_le_mul pi_gt_d6.le (exp_integer_floor 12) (by positivity) pi_pos.le
  norm_num [P] at hh ⊢
  linarith

/-- Explicit small Schoenfeld-only onset (not a Büthe invocation). -/
theorem cube_schoenfeld_1321 {n : ℝ} (hS : Schoenfeld61) (rh : RiemannHypothesis) (hn : 1321 ≤ n) :
    (0.692 : ℝ)*n^2/log n < count (n^3) ((n+1)^3) := by
  have ht : log (1321 : ℝ) ≤ (7.187 : ℝ) := by
    apply (log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1321)).mpr
    have hf := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 187/1000) 6
    norm_num [Finset.sum_range_succ] at hf
    rw [show (7.187 : ℝ) = 7+187/1000 by norm_num, exp_add]
    have hh := mul_le_mul (exp_integer_floor 7) hf (by norm_num) (exp_nonneg _)
    norm_num at hh
    exact le_trans (by norm_num) hh
  apply schoenfeld_density hS rh (by norm_num) (by norm_num) hn
    (by norm_num) ht (q := 0.462) (by norm_num) ?_ (by norm_num) (by norm_num) (by norm_num)
  have hs : (36.34 : ℝ) ≤ sqrt 1321 := (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hh := mul_le_mul pi_gt_d6.le hs (by norm_num) pi_pos.le
  norm_num [P] at hh ⊢
  linarith

private lemma cut_log : log (2154433 : ℝ) ≤ (14.58304 : ℝ) := by
  apply (log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2154433)).mpr
  have hI : (2.7182818283 : ℝ)^14 ≤ exp 14 := by
    rw [show (14 : ℝ) = (14 : ℕ) * 1 by norm_num, exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 14
  have hf := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.58304) 10
  norm_num [Finset.sum_range_succ] at hf
  rw [show (14.58304 : ℝ) = 14 + 1822/3125 by norm_num, exp_add]
  have hh := mul_le_mul hI hf (by norm_num) (exp_nonneg _)
  refine le_trans ?_ hh
  norm_num


private lemma cut_q : 3*P (14.58304 : ℝ) ≤ 8*π*(0.049515 : ℝ)*sqrt 2154433 := by
  have hs : (1467.798 : ℝ) ≤ sqrt 2154433 := (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hπ := pi_gt_d6.le
  have h := mul_le_mul hπ hs (by norm_num) pi_pos.le
  unfold P
  nlinarith

private lemma buthe_cap_of_le_cut {n : ℝ} (hn : (45/4 : ℝ) ≤ n) (hc : n ≤ 2154433) :
    (n+1)^3 ≤ (10 : ℝ)^19 :=
  (pow_le_pow_left₀ (by linarith : 0 ≤ n+1) (show n+1 ≤ 2154434 by linarith) 3).trans (by norm_num)

lemma buthe_fixed (hB : Buthe1617) {n m c : ℝ} (hm : (45/4 : ℝ) ≤ m) (hn : m ≤ n)
    (hcap : (n+1)^3 ≤ 10^19) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcert : (19/30 : ℝ)^2 ≤ (1-c)^2*m) :
    c*n^2/log n < count (n^3) ((n+1)^3) := by
  have hn0 : 0 < n := by linarith
  have hcS : (19/30 : ℝ) ≤ (1-c)*sqrt n := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, sq_sqrt hn0.le]
    exact hcert.trans (mul_le_mul_of_nonneg_left hn (sq_nonneg _))
  exact buthe_density hB (hm.trans hn) hcap hc
    (by linarith [(div_le_iff₀ (sqrt_pos.mpr hn0)).mpr hcS])

/-- Finite, unconditional relative only to the historical Büthe estimate. -/
theorem cube_buthe_081 {n : ℝ} (hB : Buthe1617) (hn : (45/4 : ℝ) ≤ n)
    (hcap : (n+1)^3 ≤ 10^19) :
    (0.81 : ℝ)*n^2/log n < count (n^3) ((n+1)^3) :=
  buthe_fixed hB (le_refl _) hn hcap (by norm_num) (by norm_num) (by norm_num)

theorem cube_buthe_090 {n : ℝ} (hB : Buthe1617) (hn : 41 ≤ n)
    (hcap : (n+1)^3 ≤ 10^19) :
    (0.90 : ℝ)*n^2/log n < count (n^3) ((n+1)^3) :=
  buthe_fixed hB (by norm_num) hn hcap (by norm_num) (by norm_num) (by norm_num)

theorem cube_buthe_095 {n : ℝ} (hB : Buthe1617) (hn : 161 ≤ n)
    (hcap : (n+1)^3 ≤ 10^19) :
    (0.95 : ℝ)*n^2/log n < count (n^3) ((n+1)^3) :=
  buthe_fixed hB (by norm_num) hn hcap (by norm_num) (by norm_num) (by norm_num)

/-- Primary hybrid bound. The historical finite-domain source and the
Schoenfeld analytic source are both disclosed, and RH is ordinary RH. -/
theorem cube_hybrid_096699 {n : ℝ} (hS : Schoenfeld61) (rh : RiemannHypothesis)
    (hB : Buthe1617) (hn : 369 ≤ n) :
    (0.96699 : ℝ)*n^2/log n < count (n^3) ((n+1)^3) := by
  by_cases hc : n ≤ 2154433
  · exact buthe_fixed hB (by norm_num) hn (buthe_cap_of_le_cut (by linarith) hc)
      (by norm_num) (by norm_num) (by norm_num)
  · exact schoenfeld_density hS rh (by norm_num) (by norm_num) (le_of_not_ge hc)
      (by norm_num) cut_log (by norm_num) cut_q (by norm_num) (by norm_num) (by norm_num)

theorem cube_exp8 {n : ℝ} (hS : Schoenfeld61) (rh : RiemannHypothesis)
    (hB : Buthe1617) (hn : exp 8 ≤ n) :
    (0.96699 : ℝ)*n^2/log n < count (n^3) ((n+1)^3) := by
  apply cube_hybrid_096699 hS rh hB (_ : (369 : ℝ) ≤ n)
  have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) 6
  norm_num [Finset.sum_range_succ] at h
  linarith


theorem cube_buthe_exp8 {n : ℝ} (hB : Buthe1617) (hn : exp 8 ≤ n)
    (hcap : (n+1)^3 ≤ 10^19) :
    (0.98839 : ℝ)*n^2/log n < count (n^3) ((n+1)^3) := by
  have he := exp_integer_floor 8
  norm_num at he
  have h2980 : (2980 : ℝ) ≤ n := by linarith
  exact buthe_fixed hB (by norm_num) h2980 hcap (by norm_num) (by norm_num) (by norm_num)

theorem cube_hybrid_early {n c : ℝ} (hS : Schoenfeld61) (rh : RiemannHypothesis)
    (hB : Buthe1617) (hn : (45/4 : ℝ) ≤ n) (hc0 : 0 ≤ c) (hc1 : c ≤ 0.96699)
    (hc2 : c ≤ 1 - (19/30 : ℝ) / sqrt n) :
    c*n^2/log n < count (n^3) ((n+1)^3) := by
  by_cases hcut : n ≤ 2154433
  · exact buthe_density hB hn (buthe_cap_of_le_cut hn hcut) hc0 hc2
  · have h369 : (369 : ℝ) ≤ n := by linarith
    have hh := cube_hybrid_096699 hS rh hB h369
    have hp : 0 ≤ log n := by linarith [log_ge_two hn]
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 (sq_nonneg n)) hp).trans_lt hh

#print axioms cube_schoenfeld_1321
#print axioms cube_schoenfeld_exp8
#print axioms cube_schoenfeld_exp16
#print axioms cube_schoenfeld_exp18
#print axioms cube_schoenfeld_exp24
#print axioms cube_buthe_exp8
#print axioms cube_hybrid_early
#print axioms endpoint_transfer
#print axioms buthe_density
#print axioms schoenfeld_density
#print axioms cube_buthe_081
#print axioms cube_buthe_090
#print axioms cube_buthe_095
#print axioms cube_hybrid_096699
#print axioms cube_exp8

end CubeTheta
