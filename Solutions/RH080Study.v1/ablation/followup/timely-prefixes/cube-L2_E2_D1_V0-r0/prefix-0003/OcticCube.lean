import ThetaCube

/-! The literal OcticFamily contract from PowerPopulation.lean, without importing
the costly upstream numerical closure; the generic set lemmas below are adapted
from /representation/source/PowerPartition.lean (Apache-2.0). -/
namespace FreshCubes.Octic
open Real Set
noncomputable section
set_option maxHeartbeats 0

def OcticFamily : Prop := ∀ C ∈ Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
  (8 / 9 * C - 18203 / 20000 + (21 / 5) / log u) * sqrt u <
    ((QuarticWindow.primesBetween u (u + C * sqrt u * log u)).card : ℝ)

lemma open_primes_subset {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    QuarticWindow.primesBetween a b ⊆ QuarticWindow.primesBetween c d := by
  classical
  intro p hp
  obtain ⟨hpB, hap, hpb⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨?_, hca.trans_lt hap, hpb.trans_le hbd⟩
  exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hpB).1.trans
    (Nat.floor_le_floor hbd), (Nat.mem_primesLE.mp hpB).2⟩

lemma open_count_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (QuarticWindow.primesBetween a b).card + (QuarticWindow.primesBetween b c).card ≤
      (QuarticWindow.primesBetween a c).card := by
  classical
  have hd : Disjoint (QuarticWindow.primesBetween a b) (QuarticWindow.primesBetween b c) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (Finset.mem_filter.mp hp).2.2
    have hq' := (Finset.mem_filter.mp hq).2.1
    linarith
  rw [← Finset.card_union_of_disjoint hd]
  apply Finset.card_le_card
  exact Finset.union_subset (open_primes_subset le_rfl hbc) (open_primes_subset hab le_rfl)

/-- Finite disjoint open cells. Prime endpoints may be omitted, never double counted. -/
theorem tiled_count {a H m : ℝ} (hH : 0 ≤ H) (k : ℕ)
    (hc : ∀ i < k, m < ((QuarticWindow.primesBetween (a + i * H) (a + (i + 1) * H)).card : ℝ)) :
    (k : ℝ) * m ≤ ((QuarticWindow.primesBetween a (a + k * H)).card : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hi := ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))
    have hcell := hc k (Nat.lt_succ_self k)
    have had := open_count_add
      (a := a) (b := a + k * H) (c := a + (k + 1) * H)
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hH)) (by nlinarith)
    have had' : ((QuarticWindow.primesBetween a (a + k * H)).card : ℝ) +
      ((QuarticWindow.primesBetween (a + k * H) (a + (k + 1) * H)).card : ℝ) ≤
        ((QuarticWindow.primesBetween a (a + (k + 1) * H)).card : ℝ) := by exact_mod_cast had
    push_cast
    nlinarith


lemma width_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    count a b ≤ count c d := by
  unfold count
  exact_mod_cast Finset.card_le_card (open_primes_subset hca hbd)

lemma exp4_lower : (27299/500 : ℝ) ≤ exp 4 := by
  have h := sum_le_exp_of_nonneg (show (0:ℝ) ≤ 4 by norm_num) 17
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
  linarith

lemma n2500 {n : ℝ} (hn : exp 8 ≤ n) : 2500 ≤ n := by
  have h := mul_le_mul exp4_lower exp4_lower (by norm_num : (0:ℝ) ≤ 27299/500)
    (exp_nonneg 4)
  rw [← exp_add, show (4:ℝ)+4 = 8 by norm_num] at h
  linarith

lemma log_bound {n u : ℝ} (h : exp 8 ≤ n) (hu : n^3 ≤ u)
    (hy : u ≤ (n+1)^3) :
    log u ≤ 3*(20001/20000)*log n := by
  have hn : 2500 ≤ n := n2500 h
  have hn0 : 0 < n := by linarith
  have hL : 8 ≤ log n := by simpa using log_le_log (exp_pos 8) h
  have hh := log_le_log ((pow_pos hn0 3).trans_le hu) hy
  rw [log_pow] at hh
  simp only [Nat.cast_ofNat] at hh
  have hstep := log_step hn0
  have hi : 1/n ≤ 1/2500 := one_div_le_one_div_of_le (by norm_num) hn
  linarith

lemma width_bound {n u : ℝ} (h : exp 8 ≤ n) (hu : n^3 ≤ u)
    (hy : u ≤ (n+1)^3) :
    sqrt u * log u ≤ (1001/1000)*(3*n*sqrt n*log n) := by
  have hn : 2500 ≤ n := n2500 h
  have hn0 : 0 < n := by linarith
  have hLu := log_bound h hu hy
  have hs : sqrt u ≤ (2501/2500)*(5001/5000)*n*sqrt n := by
    have hsC : sqrt (n+1) ≤ (5001/5000)*sqrt n := by
      apply (sqrt_le_iff).mpr ⟨by positivity, ?_⟩
      rw [mul_pow, sq_sqrt hn0.le]
      linarith
    have hC : n+1 ≤ (2501/2500)*n := by linarith
    calc
      _ ≤ sqrt ((n+1)^3) := sqrt_le_sqrt hy
      _ = (n+1)*sqrt (n+1) := sqrt_cube (by positivity)
      _ ≤ ((2501/2500)*n)*((5001/5000)*sqrt n) :=
        mul_le_mul hC hsC (sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have hL : 8 ≤ log n := by simpa using log_le_log (exp_pos 8) h
  have h1 : 1 ≤ u := (show (1:ℝ) ≤ n^3 by linarith [pow_le_pow_left₀ (show (0:ℝ) ≤ 1 by norm_num) (show 1 ≤ n by linarith) 3]).trans hu
  have h0 : 0 ≤ log u := log_nonneg h1
  refine (mul_le_mul hs hLu h0 (by positivity)).trans ?_
  have hh : 0 ≤ n*sqrt n*log n := by positivity
  nlinarith only [hh]

lemma sqrt_over_log_lower {n : ℝ} (hn : exp 8 ≤ n) :
    (27299/500)/8 ≤ sqrt n/log n := by
  have hn0 : 0 < n := (exp_pos 8).trans_le hn
  have hL : 8 ≤ log n := by simpa using log_le_log (exp_pos 8) hn
  have hL0 : 0 < log n := by linarith
  let v := log n-8
  have hv : 0 ≤ v := sub_nonneg.mpr hL
  have he := add_one_le_exp (v/2)
  have hr : sqrt n = exp 4 * exp (v/2) := by
    rw [← exp_add, show 4+v/2 = log n/2 by dsimp [v]; ring,
       ← log_sqrt hn0.le, exp_log (sqrt_pos.mpr hn0)]
  have hmul := mul_le_mul exp4_lower he (show 0 ≤ v/2+1 by positivity) (exp_nonneg 4)
  rw [← hr] at hmul
  apply (le_div_iff₀ hL0).mpr
  dsimp [v] at hmul
  linarith

lemma small_width_log {n : ℝ} (hn : exp 8 ≤ n) (hs : sqrt n/log n < 19) :
    log n < 11 := by
  by_contra! hL
  have hn0 := (exp_pos 8).trans_le hn
  have hL0 : 0 < log n := by linarith
  let v := log n-11
  have hv : 0 ≤ v := sub_nonneg.mpr hL
  have he := add_one_le_exp (v/2)
  have h55 : (210:ℝ) ≤ exp (11/2) := by
    have hh := sum_le_exp_of_nonneg (show (0:ℝ) ≤ 11/2 by norm_num) 9
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at hh ⊢
    linarith
  have hr : sqrt n = exp (11/2) * exp (v/2) := by
    rw [← exp_add, show 11/2+v/2 = log n/2 by dsimp [v]; ring,
       ← log_sqrt hn0.le, exp_log (sqrt_pos.mpr hn0)]
  have hmul := mul_le_mul h55 he (show 0 ≤ v/2+1 by positivity) (exp_nonneg (11/2))
  rw [← hr] at hmul
  have hsm := (div_lt_iff₀ hL0).mp hs
  dsimp [v] at hmul
  linarith

/-- A single unslacked cell attains the target even at the onset. -/
theorem single_78117 (hf : OcticFamily) {n : ℝ} (hn : exp 8 ≤ n)
    (hs : sqrt n/log n ≤ 16) :
    (78117/100000:ℝ)*(n^2/log n) < count (n^3) ((n+1)^3) := by
  have hn0 := (exp_pos 8).trans_le hn
  have hL : 8 ≤ log n := by simpa using log_le_log (exp_pos 8) hn
  have hL0 : 0 < log n := by linarith
  have ha : exp 24 ≤ n^3 := by
    have h := pow_le_pow_left₀ (exp_nonneg 8) hn 3
    simpa only [← exp_nat_mul, show (3:ℕ)*(8:ℝ)=24 by norm_num] using h
  let C := sqrt n/log n
  have hC : C ∈ Icc (103/100:ℝ) 16 := ⟨by dsimp [C]; linarith [sqrt_over_log_lower hn], hs⟩
  have hF := hf C hC _ ha
  rw [sqrt_cube hn0.le, log_pow] at hF
  norm_num only [Nat.cast_ofNat] at hF
  have hwidth : C*(n*sqrt n)*(3*log n) = 3*n^2 := by
    dsimp [C]
    calc
      _ = 3*n*(sqrt n)^2*(log n/log n) := by ring
      _ = _ := by rw [sq_sqrt hn0.le, div_self hL0.ne']; ring
  rw [hwidth] at hF
  have hsub : count (n^3) (n^3+3*n^2) ≤ count (n^3) ((n+1)^3) :=
    width_mono le_rfl (by nlinarith only [hn0])
  let a : ℝ := 8/9-78117/100000
  let v := log n-8
  have hv : 0 ≤ v := sub_nonneg.mpr hL
  have he := add_one_le_exp (v/2)
  have hr : sqrt n = exp 4 * exp (v/2) := by
    rw [← exp_add, show 4+v/2 = log n/2 by dsimp [v]; ring,
       ← log_sqrt hn0.le, exp_log (sqrt_pos.mpr hn0)]
  have hmul := mul_le_mul exp4_lower he (show 0 ≤ v/2+1 by positivity) (exp_nonneg 4)
  rw [← hr] at hmul
  have hdebt : (18203/20000)*log n-7/5 ≤ a*sqrt n := by
    have hh := mul_le_mul_of_nonneg_left hmul (show 0 ≤ a by norm_num [a])
    dsimp [a,v] at hh
    linarith
  have hcoef : (78117/100000:ℝ)*C ≤ 8/9*C-18203/20000+(21/5)/(3*log n) := by
    dsimp [C]
    field_simp [hL0.ne']
    linarith [hdebt]
  have hProd := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ n*sqrt n by positivity)
  have heq : (78117/100000:ℝ)*C*(n*sqrt n) = (78117/100000)*(n^2/log n) := by
    dsimp [C]
    calc
      _ = (78117/100000)*(n*(sqrt n)^2/log n) := by ring
      _ = _ := by rw [sq_sqrt hn0.le]; ring
  rw [heq] at hProd
  exact hProd.trans_lt (hF.trans_le hsub)


/-- For large widths, tile with the minimum possible conservative ceil count.
Use the logarithmic bonus only in the short band that needs it. -/
theorem tiles_78117 (hf : OcticFamily) {n : ℝ} (hn : exp 8 ≤ n)
    (hs16 : 16 < sqrt n/log n) :
    (78117/100000:ℝ)*(n^2/log n) < count (n^3) ((n+1)^3) := by
  have hn0 := (exp_pos 8).trans_le hn
  have hL : 8 ≤ log n := by simpa using log_le_log (exp_pos 8) hn
  have hL0 : 0 < log n := by linarith
  have ha : exp 24 ≤ n^3 := by
    have h := pow_le_pow_left₀ (exp_nonneg 8) hn 3
    simpa only [← exp_nat_mul, show (3:ℕ)*(8:ℝ)=24 by norm_num] using h
  let s := sqrt n/log n
  let k : ℕ := ⌈s/16⌉₊
  let C := s/((1001/1000)*(k:ℝ))
  let H := 3*n^2/(k:ℝ)
  let d : ℝ := if s<19 then 15803/20000 else 18203/20000
  have hs : 0 < s := by dsimp [s]; positivity
  have hklo : s/16 ≤ (k:ℝ) := Nat.le_ceil _
  have hkhi : (k:ℝ) < s/16+1 := Nat.ceil_lt_add_one (by positivity)
  have hkpos : 0 < (k:ℝ) := (by positivity : 0<s/16).trans_le hklo
  have hk2 : (k:ℝ) < s/8 := by change 16 < s at hs16; linarith
  have hH : 0 < H := by dsimp [H]; positivity
  have hC : C ∈ Icc (103/100:ℝ) 16 := by
    constructor
    · change (103/100:ℝ) ≤ s/((1001/1000)*(k:ℝ))
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    · change s/((1001/1000)*(k:ℝ)) ≤ (16:ℝ)
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
  have hd0 : 0 ≤ d := by dsimp [d]; split <;> norm_num
  have hdhi : d ≤ (18203/20000:ℝ) := by dsimp [d]; split <;> norm_num
  have hg0 : 0 ≤ (8/9:ℝ)*C-d := by linarith [hC.1]
  have hkC : (k:ℝ)*C = (1000/1001)*s := by
    dsimp [C]
    field_simp [hkpos.ne']
  have hCH : C*((1001/1000)*(3*n*sqrt n*log n)) = H := by
    dsimp [C,H,s]
    field_simp [hkpos.ne',hL0.ne']
    ring_nf
    rw [sq_sqrt hn0.le]
  have hkH : (k:ℝ)*H = 3*n^2 := by dsimp [H]; field_simp [hkpos.ne']
  have hY : n^3 + (k:ℝ)*H ≤ (n+1)^3 := by rw [hkH]; nlinarith only [hn0]
  have hc : ∀ i < k, ((8/9:ℝ)*C-d)*(n*sqrt n) <
      ((QuarticWindow.primesBetween (n^3+(i:ℝ)*H) (n^3+(i+1:ℝ)*H)).card:ℝ) := by
    intro i hi
    let u := n^3+(i:ℝ)*H
    have hik : (i+1:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hi
    have hux : n^3 ≤ u := by dsimp [u]; exact le_add_of_nonneg_right (by positivity)
    have hui : u ≤ n^3+(i+1:ℝ)*H := by dsimp [u]; nlinarith only [hH]
    have hiy : n^3+(i+1:ℝ)*H ≤ (n+1)^3 := by
      exact (show n^3+(i+1:ℝ)*H ≤ n^3+(k:ℝ)*H by gcongr).trans hY
    have huy := hui.trans hiy
    have hBu := width_bound hn hux huy
    have hW := mul_le_mul_of_nonneg_left hBu (show 0 ≤ C from (by norm_num : 0 ≤ (103/100:ℝ)).trans hC.1)
    rw [hCH] at hW
    have hU : exp 24 ≤ u := ha.trans hux
    have huL : 24 ≤ log u := by simpa using log_le_log (exp_pos 24) hU
    have huL0 : 0 < log u := by linarith
    have hD : (18203/20000:ℝ)-d ≤ (21/5)/log u := by
      dsimp [d]
      split
      · rename_i hsm
        have hL' := small_width_log hn hsm
        have huL' := log_bound hn hux huy
        apply (le_div_iff₀ huL0).mpr
        linarith
      · simp
        positivity
    have hcoef : (8/9:ℝ)*C-d ≤ (8/9)*C-18203/20000+(21/5)/log u := by linarith
    have hroot := sqrt_le_sqrt hux
    rw [sqrt_cube hn0.le] at hroot
    have hlow := mul_le_mul hcoef hroot (by positivity : 0 ≤ n*sqrt n)
      (hg0.trans hcoef)
    have hsub : count u (u+C*sqrt u*log u) ≤ count u (n^3+(i+1:ℝ)*H) :=
      width_mono le_rfl (by dsimp [u] at *; nlinarith only [hW])
    exact hlow.trans_lt ((hf C hC u hU).trans_le hsub)
  have htile := tiled_count hH.le k hc
  have hsub : count (n^3) (n^3+(k:ℝ)*H) ≤ count (n^3) ((n+1)^3) :=
    width_mono le_rfl hY
  have hcoef : (78117/100000:ℝ)*s < (k:ℝ)*((8/9:ℝ)*C-d) := by
    by_cases hsm : s<19
    · have hh := mul_lt_mul_of_pos_left hk2 (by norm_num : (0:ℝ) < 15803/20000)
      rw [show d=(15803/20000:ℝ) by simp [d,hsm]]
      nlinarith only [hh,hkC,hs]
    · have hb : (k:ℝ) < (1/16+1/19)*s := by linarith
      have hh := mul_lt_mul_of_pos_left hb (by norm_num : (0:ℝ) < 18203/20000)
      rw [show d=(18203/20000:ℝ) by simp [d,hsm]]
      nlinarith only [hh,hkC,hs]
  have hp := mul_lt_mul_of_pos_right hcoef (show 0 < n*sqrt n by positivity)
  have he : (78117/100000:ℝ)*s*(n*sqrt n) = (78117/100000)*(n^2/log n) := by
    dsimp [s]
    calc
      _ = (78117/100000)*(n*(sqrt n)^2/log n) := by ring
      _ = _ := by rw [sq_sqrt hn0.le]; ring
  rw [he, mul_assoc] at hp
  exact hp.trans_le (htile.trans hsub)

theorem cube_78117 (hf : OcticFamily) {n : ℝ} (hn : exp 8 ≤ n) :
    (78117/100000:ℝ)*(n^2/log n) < count (n^3) ((n+1)^3) := by
  by_cases h : sqrt n/log n ≤ 16
  · exact single_78117 hf hn h
  · exact tiles_78117 hf hn (lt_of_not_ge h)

#print axioms single_78117
#print axioms tiles_78117
#print axioms cube_78117
end
end FreshCubes.Octic
