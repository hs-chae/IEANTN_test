import ThetaTransfer

noncomputable section
open Real
namespace CubeStudy

lemma cubic_sqrt {n : ℝ} (hn : 0 ≤ n) : sqrt (n^3) = n * sqrt n := by
  rw [show n^3 = n^2*n by ring, sqrt_mul (sq_nonneg n), sqrt_sq hn]

lemma log_succ {n : ℝ} (hn : 0 < n) : log (n+1) ≤ log n + 1/n := by
  have h : 0 < 1 + 1/n := by positivity
  have hlog := log_le_sub_one_of_pos h
  have he : n+1 = n*(1+1/n) := by field_simp
  rw [he, log_mul hn.ne' h.ne']
  linarith

lemma main_cube {n : ℝ} (hn : 0 < n) (hL : 1 ≤ log n) :
    n^2 / log n ≤ ((n+1)^3-n^3) / (3*log (n+1)) := by
  have hL0 : 0 < log n := by linarith
  have hp : 0 < log (n+1) := log_pos (by linarith)
  have hp' : log (n+1) ≤ log n * (1+1/n) := by
    have hh := mul_le_mul_of_nonneg_right hL (show 0 ≤ 1/n by positivity)
    linarith [log_succ hn, show log n*(1+1/n) = log n + log n*(1/n) by ring]
  have hm := mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ 3*n^2/log n)
  have he : 3*n^2/log n * (log n*(1+1/n)) = 3*n^2+3*n := by field_simp <;> ring
  rw [he] at hm
  apply (le_div_iff₀ (by positivity : 0 < 3*log (n+1))).mpr
  linarith [show n^2/log n*(3*log (n+1)) = 3*n^2/log n*log (n+1) by ring,
    show (n+1)^3-n^3 = 3*n^2+3*n+1 by ring]

lemma sqrt_succ_bounded {n : ℝ} (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a)
    (h : (1+1/n)^3 ≤ (1+a/n)^2) :
    sqrt ((n+1)^3) ≤ (1+a/n)*(n*sqrt n) := by
  apply (sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hm := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ n^3)
  have e1 : (1+1/n)^3*n^3 = (n+1)^3 := by field_simp
  have e2 : (1+a/n)^2*n^3 = ((1+a/n)*(n*sqrt n))^2 := by
    rw [mul_pow, mul_pow, sq_sqrt hn.le]
    ring
  rwa [e1,e2] at hm

lemma sqrt_succ_two {n : ℝ} (hn : 1 ≤ n) :
    sqrt ((n+1)^3) ≤ (1+2/n)*(n*sqrt n) := by
  have hn0 : 0 < n := by linarith
  apply sqrt_succ_bounded hn0 2 (by norm_num)
  have hr : 1/n ≤ 1 := (div_le_iff₀ hn0).mpr (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg (1/n)),
    sq_nonneg (1/n), show 0 ≤ 1/n by positivity,
    show 2/n=2*(1/n) by ring]

lemma sqrt_succ_buthe {n : ℝ} (hn : 12 ≤ n) :
    sqrt ((n+1)^3) ≤ (1+(8/5)/n)*(n*sqrt n) := by
  have hn0 : 0 < n := by linarith
  apply sqrt_succ_bounded hn0 (8/5) (by norm_num)
  let r := 1/n
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hR : r ≤ 1/12 := (div_le_iff₀ hn0).mpr (by linarith)
  have hR2 : r^2 ≤ 1/144 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hR)]
  have hq : 0 ≤ 1/5-(11/25)*r-r^2 := by linarith
  have he : (8/5:ℝ)/n = (8/5)*r := by dsimp [r]; ring
  rw [he]
  change (1+r)^3 ≤ (1+(8/5)*r)^2
  nlinarith [mul_nonneg hr hq]

def schoenfeldLoss (n : ℝ) : ℝ :=
  (1+1/n)*log n*(3*log n-2+3/n)/(4*π*sqrt n)

lemma schoenfeld_cube_pointwise (hs : Schoenfeld) (rh : RiemannHypothesis)
    {n : ℝ} (hn : 1 ≤ n) (hL : 8 ≤ log n) (hx : 2300000000 ≤ n^3) :
    (1-schoenfeldLoss n)*(n^2/log n) < count (n^3) ((n+1)^3) := by
  have hn0 : 0 < n := by linarith
  have hxy : n^3 < (n+1)^3 := pow_lt_pow_left₀ (by linarith) hn0.le (by decide)
  have hL0 : 0 < log n := by linarith
  have hLp : 0 < log (n+1) := log_pos (by linarith)
  have hlog := log_le_log hn0 (by linarith : n ≤ n+1)
  have hS : 0 < sqrt n := sqrt_pos.mpr hn0
  have he := schoenfeld_window hs rh hx hxy
  have hm := main_cube hn0 (show 1 ≤ log n by linarith)
  have hE : err (n^3) + err ((n+1)^3) ≤
        ((1+1/n)*(n*sqrt n)*(3*log (n+1)-2)/(4*π))*(3*log (n+1)) := by
    unfold err
    simp only [log_pow, Nat.cast_ofNat]
    have hF : (3*log n-2)*(3*log n) ≤ (3*log (n+1)-2)*(3*log (n+1)) := by
      apply mul_le_mul <;> linarith
    have hnon : 0 ≤ (3*log (n+1)-2)*(3*log (n+1)) :=
      mul_nonneg (by linarith) (by linarith)
    have h1 := mul_le_mul_of_nonneg_left hF (sqrt_nonneg (n^3))
    have h2 := mul_le_mul_of_nonneg_right (sqrt_succ_two hn) hnon
    rw [cubic_sqrt hn0.le] at h1 ⊢
    have h3 : 0 < 8*π := by positivity
    have h4 := div_le_div_of_nonneg_right (add_le_add h1 h2) h3.le
    rw [add_div] at h4
    convert h4 using 1 <;> first | rfl | ring
  have hE' :
      (err (n^3)+err ((n+1)^3))/(3*log (n+1)) ≤
      (1+1/n)*(n*sqrt n)*(3*log (n+1)-2)/(4*π) :=
    (div_le_iff₀ (by positivity)).mpr hE
  have hM : ((n+1)^3-n^3)/(3*log (n+1)) -
      (err (n^3)+err ((n+1)^3))/(3*log (n+1)) < count (n^3) ((n+1)^3) := by
    rw [← sub_div]
    apply (div_lt_iff₀ (by positivity)).mpr
    rw [log_pow] at he
    norm_num at he
    linarith
  have hUp := log_succ hn0
  have hE2 : (1+1/n)*(n*sqrt n)*(3*log (n+1)-2)/(4*π) ≤
      schoenfeldLoss n*(n^2/log n) := by
    have hh := mul_le_mul_of_nonneg_left (show 3*log (n+1)-2 ≤ 3*log n-2+3/n by linarith [show (3:ℝ)/n=3*(1/n) by ring])
      (show 0 ≤ (1+1/n)*(n*sqrt n) by positivity)
    apply (div_le_div_of_nonneg_right hh (by positivity : 0 ≤ 4*π)).trans_eq
    unfold schoenfeldLoss
    field_simp
    ring_nf
    rw [sq_sqrt hn0.le]
    ring
  nlinarith only [hM,hm,hE',hE2]

def butheLoss (n : ℝ) : ℝ := (19/30 + 26/(25*n))/sqrt n

lemma buthe_cube_pointwise (hb : Buthe) {n : ℝ} (hn : 12 ≤ n)
    (hL : 1 ≤ log n) (hy : (n+1)^3 ≤ 10^19) :
    (1-butheLoss n)*(n^2/log n) < count (n^3) ((n+1)^3) := by
  have hn0 : 0 < n := by linarith
  have hx : 1423 ≤ n^3 := (by norm_num : (1423:ℝ) ≤ 12^3).trans
    (pow_le_pow_left₀ (by norm_num) hn 3)
  have hxy : n^3 < (n+1)^3 := pow_lt_pow_left₀ (by linarith) hn0.le (by decide)
  have hL0 : 0 < log n := by linarith
  have hLp : 0 < log (n+1) := log_pos (by linarith)
  have hlog := log_le_log hn0 (by linarith : n ≤ n+1)
  have hS : 0 < sqrt n := sqrt_pos.mpr hn0
  have he := buthe_window hb hx hxy hy
  rw [log_pow] at he
  norm_num at he
  have hm := main_cube hn0 (show 1 ≤ log n by linarith)
  have hM : ((n+1)^3-n^3)/(3*log (n+1)) -
      ((195/100:ℝ)*sqrt ((n+1)^3)-(5/100:ℝ)*sqrt (n^3))/(3*log (n+1))
      < count (n^3) ((n+1)^3) := by
    rw [← sub_div]
    exact (div_lt_iff₀ (by positivity)).mpr (by linarith)
  have hE1 : (195/100:ℝ)*sqrt ((n+1)^3)-(5/100:ℝ)*sqrt (n^3) ≤
      (19/10+78/(25*n))*(n*sqrt n) := by
    rw [cubic_sqrt hn0.le]
    have hh := mul_le_mul_of_nonneg_left (sqrt_succ_buthe hn) (by norm_num : (0:ℝ) ≤ 195/100)
    linarith [show (195/100:ℝ)*((1+(8/5)/n)*(n*sqrt n))
      - (5/100)*(n*sqrt n) = (19/10+78/(25*n))*(n*sqrt n) by ring]
  have hE2 : ((195/100:ℝ)*sqrt ((n+1)^3)-(5/100:ℝ)*sqrt (n^3))/(3*log (n+1)) ≤
      butheLoss n*(n^2/log n) := by
    calc
      _ ≤ ((19/10+78/(25*n))*(n*sqrt n))/(3*log (n+1)) :=
        div_le_div_of_nonneg_right hE1 (by positivity)
      _ ≤ ((19/10+78/(25*n))*(n*sqrt n))/(3*log n) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = _ := by
        unfold butheLoss
        field_simp
        ring_nf
        rw [sq_sqrt hn0.le]
        ring
  nlinarith only [hM,hm,hE2]

end CubeStudy
