/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
set_option autoImplicit false
noncomputable section
open Real Set Finset
namespace RH080Next.Primal

/-- Elementary exponential secant bound, with no prime-counting input. -/
theorem exp_difference_le (a b : ℝ) : exp b-exp a≤(b-a)*exp b := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (a-b)) (exp_pos b).le
  have he : exp (a-b)*exp b=exp a := by rw [← exp_add]; congr 1; ring
  rw [he] at h
  nlinarith

/-- A fixed exponent's root interval is narrow, even when its roots are very
large. The estimate uses the log-window length rather than counting all roots
up to the upper endpoint. -/
theorem prime_power_root_window_width (L δ : ℝ) (hδ : 0≤δ) (hupper : 0≤L+δ)
    (k : ℕ) (hk : 2≤k) :
    exp ((L+δ)/(k:ℝ))-exp ((L-δ)/(k:ℝ))≤δ*exp ((L+δ)/2) := by
  have hk' : (2:ℝ)≤k := by exact_mod_cast hk
  have hk0 : (0:ℝ)<k := by linarith
  have hquot : (L+δ)/(k:ℝ)≤(L+δ)/2 :=
    div_le_div_of_nonneg_left hupper (by norm_num) hk'
  have hspan : (L+δ)/(k:ℝ)-(L-δ)/(k:ℝ)≤δ := by
    rw [← sub_div]
    apply (div_le_iff₀ hk0).mpr
    nlinarith
  have hb := exp_difference_le ((L-δ)/(k:ℝ)) ((L+δ)/(k:ℝ))
  exact hb.trans ((mul_le_mul_of_nonneg_right hspan (exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hquot) hδ))

/-- Count integers in a real interval by its length plus one, including every
possible endpoint rounding. -/
theorem nat_interval_card_le (a b : ℝ) (ha : 0≤a) (hab : a≤b) :
    ((Finset.Icc (Nat.ceil a) (Nat.floor b)).card:ℝ)≤b-a+1 := by
  rw [Nat.card_Icc]
  by_cases h : Nat.ceil a≤Nat.floor b+1
  · rw [Nat.cast_sub h,Nat.cast_add,Nat.cast_one]
    have hf := Nat.floor_le (ha.trans hab)
    have hc := Nat.le_ceil a
    linarith
  · rw [Nat.sub_eq_zero_of_le (by omega : Nat.floor b+1≤Nat.ceil a)]
    norm_num
    linarith

def primePowerRootCandidates (L δ : ℝ) (k : ℕ) : Finset ℕ :=
  Finset.Icc (Nat.ceil (exp ((L-δ)/(k:ℝ)))) (Nat.floor (exp ((L+δ)/(k:ℝ))))

theorem primePowerRootCandidates_card_le (L δ : ℝ) (hδ : 0≤δ) (hupper : 0≤L+δ)
    (k : ℕ) (hk : 2≤k) :
    ((primePowerRootCandidates L δ k).card:ℝ)≤1+δ*exp ((L+δ)/2) := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have horder : exp ((L-δ)/(k:ℝ))≤exp ((L+δ)/(k:ℝ)) := by
    apply exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (by linarith) hk0.le
  have hcard := nat_interval_card_le (exp ((L-δ)/(k:ℝ))) (exp ((L+δ)/(k:ℝ)))
    (exp_pos _).le horder
  have hwidth := prime_power_root_window_width L δ hδ hupper k hk
  unfold primePowerRootCandidates
  linarith

/-- Nonprime points in the von-Mangoldt support have exponent at least two. -/
theorem nonprime_prime_power_representation {n : ℕ} (hpow : IsPrimePow n)
    (hnprime : ¬Nat.Prime n) :
    ∃ p k : ℕ, p.Prime ∧ 2≤k ∧ p^k=n := by
  rcases hpow with ⟨p,k,hp,hk,he⟩
  have hp' := hp.nat_prime
  have hk1 : k≠1 := by
    intro h
    rw [h,pow_one] at he
    exact hnprime (he ▸ hp')
  exact ⟨p,k,hp',by omega,he⟩

/-- Recover the exponent cutoff, exact root interval, and the sharper log(p)
weight bound from the actual prime-power/log-window conditions. -/
theorem prime_power_log_window_data (p k : ℕ) (hp : p.Prime) (hk : 2≤k)
    (L δ : ℝ) (hlo : L-δ≤log ((p^k:ℕ):ℝ))
    (hhi : log ((p^k:ℕ):ℝ)≤L+δ) :
    (k:ℝ)≤(L+δ)/log 2 ∧ p∈primePowerRootCandidates L δ k ∧
      log (p:ℝ)≤(L+δ)/2 := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ)<p := by linarith
  have hk2 : (2:ℝ)≤k := by exact_mod_cast hk
  have hk0 : (0:ℝ)<k := by linarith
  have hlog2 : (0:ℝ)<log 2 := log_pos (by norm_num)
  have hlogp : log 2≤log (p:ℝ) := log_le_log (by norm_num) hp2
  have hlog : log ((p^k:ℕ):ℝ)=(k:ℝ)*log (p:ℝ) := by rw [Nat.cast_pow,log_pow]
  rw [hlog] at hlo hhi
  refine ⟨(le_div_iff₀ hlog2).mpr ?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left hlogp hk0.le).trans hhi
  · have hpl : exp ((L-δ)/(k:ℝ))≤(p:ℝ) := by
      rw [← exp_log hp0]
      exact exp_le_exp.mpr ((div_le_iff₀ hk0).mpr (by nlinarith))
    have hpu : (p:ℝ)≤exp ((L+δ)/(k:ℝ)) := by
      rw [← exp_log hp0]
      exact exp_le_exp.mpr ((le_div_iff₀ hk0).mpr (by nlinarith))
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hpl,(Nat.le_floor_iff (exp_pos _).le).mpr hpu⟩
  · nlinarith [mul_le_mul_of_nonneg_right hk2 (hlog2.le.trans hlogp)]

/-- All nonprime prime powers in the exact log window, with a finite upper
envelope that is derived from the window rather than separately assumed. -/
def nonprimePrimePowerWindow (L δ : ℝ) : Finset ℕ :=
  (Finset.Icc 2 (Nat.floor (exp (L+δ)))).filter
    (fun n => ¬Nat.Prime n ∧ IsPrimePow n ∧ L-δ≤log (n:ℝ))

/-- Exhaustive cardinal estimate by exponent fibers. Counting all integers up
to sqrt(Y+) would lose the crucial narrow-window factor and is not used. -/
theorem nonprimePrimePowerWindow_card_le (L δ : ℝ) (hδ : 0≤δ) (hupper : 0≤L+δ) :
    ((nonprimePrimePowerWindow L δ).card:ℝ)≤
      ((L+δ)/log 2)*(1+δ*exp ((L+δ)/2)) := by
  let K : Finset ℕ := Finset.Icc 2 (Nat.floor ((L+δ)/log 2))
  let images (k : ℕ) : Finset ℕ := (primePowerRootCandidates L δ k).image (fun p => p^k)
  have hcover : nonprimePrimePowerWindow L δ⊆K.biUnion images := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc,hnprime,hnpow,hnlo⟩
    obtain ⟨p,k,hp,hk,he⟩ := nonprime_prime_power_representation hnpow hnprime
    have hn2 := (Finset.mem_Icc.mp hnIcc).1
    have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hnu : (n:ℝ)≤exp (L+δ) := by
      have h : (n:ℝ)≤(Nat.floor (exp (L+δ)):ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hnIcc).2
      exact h.trans (Nat.floor_le (exp_pos _).le)
    have hnhi : log (n:ℝ)≤L+δ := (log_le_iff_le_exp hn0).mpr hnu
    obtain ⟨hkbound,hroot,hlogp⟩ := prime_power_log_window_data p k hp hk L δ
      (by simpa only [he] using hnlo) (by simpa only [he] using hnhi)
    have hkfloor : k≤Nat.floor ((L+δ)/log 2) :=
      (Nat.le_floor_iff (div_nonneg hupper (log_pos (by norm_num : (1:ℝ)<2)).le)).mpr hkbound
    exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_Icc.mpr ⟨hk,hkfloor⟩,
      Finset.mem_image.mpr ⟨p,hroot,he⟩⟩
  have hKnat : K.card≤Nat.floor ((L+δ)/log 2) := by
    dsimp [K]
    rw [Nat.card_Icc]
    omega
  have hK : (K.card:ℝ)≤(L+δ)/log 2 :=
    (show (K.card:ℝ)≤(Nat.floor ((L+δ)/log 2):ℝ) by exact_mod_cast hKnat).trans
      (Nat.floor_le (div_nonneg hupper (log_pos (by norm_num : (1:ℝ)<2)).le))
  calc
    ((nonprimePrimePowerWindow L δ).card:ℝ)≤((K.biUnion images).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ k ∈ K, ((images k).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ k ∈ K, (1+δ*exp ((L+δ)/2)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hi : ((images k).card:ℝ)≤((primePowerRootCandidates L δ k).card:ℝ) := by
        exact_mod_cast Finset.card_image_le
      exact hi.trans (primePowerRootCandidates_card_le L δ hδ hupper k (Finset.mem_Icc.mp hk).1)
    _ = (K.card:ℝ)*(1+δ*exp ((L+δ)/2)) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (by positivity)

def weightedNaturalWindow (W : ℝ → ℝ) (d L : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n*W ((log (n:ℝ)-L)/d)/sqrt (n:ℝ)
def nonprimeNaturalWindow (W : ℝ → ℝ) (d L : ℝ) (n : ℕ) : ℝ :=
  if Nat.Prime n then 0 else |weightedNaturalWindow W d L n|
def primePowerWindowAllowance (M L δ : ℝ) : ℝ :=
  M*(L+δ)^2/(2*log 2*exp ((L-δ)/2))*(1+δ*exp ((L+δ)/2))

/-- The genuine von-Mangoldt function and actual spectrum support confine every
nonzero nonprime summand to the exhaustively counted finite window. -/
theorem nonprimeNaturalWindow_eq_zero_outside (W : ℝ → ℝ) (d L R : ℝ)
    (hd : 0<d) (hsupport : ∀ v : ℝ, R≤|v| → W v=0)
    (n : ℕ) (hn : n∉nonprimePrimePowerWindow L (R*d)) :
    nonprimeNaturalWindow W d L n=0 := by
  by_cases hp : Nat.Prime n
  · simp [nonprimeNaturalWindow,hp]
  unfold nonprimeNaturalWindow
  rw [ite_eq_right hp]
  by_cases hΛ : ArithmeticFunction.vonMangoldt n=0
  · simp [weightedNaturalWindow,hΛ]
  by_cases hW : W ((log (n:ℝ)-L)/d)=0
  · simp [weightedNaturalWindow,hW]
  have hpow := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  have hn2 : 2≤n := by
    have h0 := hpow.ne_zero
    have h1 := hpow.ne_one
    omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have harg : |(log (n:ℝ)-L)/d|<R := by
    apply lt_of_not_ge
    intro h
    exact hW (hsupport _ h)
  have hlow : L-R*d≤log (n:ℝ) := by
    have h := (lt_div_iff₀ hd).mp (abs_lt.mp harg).1
    linarith
  have hupp : log (n:ℝ)≤L+R*d := by
    have h := (div_lt_iff₀ hd).mp (abs_lt.mp harg).2
    linarith
  have hnupper : n≤Nat.floor (exp (L+R*d)) :=
    (Nat.le_floor_iff (exp_pos _).le).mpr ((log_le_iff_le_exp hn0).mp hupp)
  exact False.elim (hn (Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hn2,hnupper⟩,hp,hpow,hlow⟩))

/-- Each actual prime-power term uses log(p), not log(n), and the denominator
is bounded at the actual lower log-window endpoint. -/
theorem nonprimeNaturalWindow_mem_le (W : ℝ → ℝ) (d L δ M : ℝ)
    (hM : 0≤M) (hupper : 0≤L+δ) (hbound : ∀ v : ℝ, |W v|≤M)
    (n : ℕ) (hn : n∈nonprimePrimePowerWindow L δ) :
    nonprimeNaturalWindow W d L n≤M*(L+δ)/(2*exp ((L-δ)/2)) := by
  rcases Finset.mem_filter.mp hn with ⟨hnIcc,hnprime,hnpow,hnlo⟩
  obtain ⟨p,k,hp,hk,he⟩ := nonprime_prime_power_representation hnpow hnprime
  have hn2 := (Finset.mem_Icc.mp hnIcc).1
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnu : (n:ℝ)≤exp (L+δ) := by
    have h : (n:ℝ)≤(Nat.floor (exp (L+δ)):ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hnIcc).2
    exact h.trans (Nat.floor_le (exp_pos _).le)
  have hnhi := (log_le_iff_le_exp hn0).mpr hnu
  have hdata := prime_power_log_window_data p k hp hk L δ
    (by simpa only [he] using hnlo) (by simpa only [he] using hnhi)
  have hΛ : ArithmeticFunction.vonMangoldt n=log (p:ℝ) := by
    rw [← he,ArithmeticFunction.vonMangoldt_apply_pow (by omega : k≠0),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hp1 : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by have h:=hp.two_le; omega)
  have hΛ0 : 0≤ArithmeticFunction.vonMangoldt n := by rw [hΛ]; exact log_nonneg hp1
  have hΛupper : ArithmeticFunction.vonMangoldt n≤(L+δ)/2 := by rw [hΛ]; exact hdata.2.2
  have hExpLower : exp (L-δ)≤(n:ℝ) := (le_log_iff_exp_le hn0).mp hnlo
  have hsq : exp ((L-δ)/2)^2=exp (L-δ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hroot : exp ((L-δ)/2)≤sqrt (n:ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n),sqrt_nonneg (n:ℝ),exp_pos ((L-δ)/2)]
  unfold nonprimeNaturalWindow weightedNaturalWindow
  rw [ite_eq_right hnprime,abs_div,abs_mul,abs_of_nonneg hΛ0,abs_of_nonneg (sqrt_nonneg _)]
  have hnum : ArithmeticFunction.vonMangoldt n*|W ((log (n:ℝ)-L)/d)|≤(L+δ)/2*M :=
    mul_le_mul hΛupper (hbound _) (abs_nonneg _) (by positivity)
  calc
    _ ≤ ((L+δ)/2*M)/sqrt (n:ℝ) :=
      div_le_div_of_nonneg_right hnum (sqrt_nonneg _)
    _ ≤ ((L+δ)/2*M)/exp ((L-δ)/2) :=
      div_le_div_of_nonneg_left (by positivity) (exp_pos _) hroot
    _ = _ := by ring

/-- Complete genuine nonprime prime-power allowance, including convergence.
No prime-power count or output value is an unverified premise. -/
theorem tsum_nonprimeNaturalWindow_le (W : ℝ → ℝ) (d L R M : ℝ)
    (hd : 0<d) (hR : 0≤R) (hM : 0≤M) (hupper : 0≤L+R*d)
    (hsupport : ∀ v : ℝ, R≤|v| → W v=0) (hbound : ∀ v : ℝ, |W v|≤M) :
    Summable (nonprimeNaturalWindow W d L) ∧
      (∑' n : ℕ, nonprimeNaturalWindow W d L n)≤primePowerWindowAllowance M L (R*d) := by
  have hzero := nonprimeNaturalWindow_eq_zero_outside W d L R hd hsupport
  have hsum : Summable (nonprimeNaturalWindow W d L) := summable_of_ne_finset_zero hzero
  refine ⟨hsum,?_⟩
  rw [tsum_eq_sum hzero]
  let cap : ℝ := M*(L+R*d)/(2*exp ((L-R*d)/2))
  have hcap : 0≤cap := by dsimp [cap]; positivity
  have hterm (n : ℕ) (hn : n∈nonprimePrimePowerWindow L (R*d)) :
      nonprimeNaturalWindow W d L n≤cap :=
    nonprimeNaturalWindow_mem_le W d L (R*d) M hM hupper hbound n hn
  have htotal := Finset.sum_le_sum hterm
  rw [Finset.sum_const,nsmul_eq_mul] at htotal
  have hcard := nonprimePrimePowerWindow_card_le L (R*d) (mul_nonneg hR hd.le) hupper
  apply htotal.trans
  apply (mul_le_mul_of_nonneg_right hcard hcap).trans_eq
  unfold cap primePowerWindowAllowance
  ring

#print axioms prime_power_root_window_width
#print axioms nat_interval_card_le
#print axioms primePowerRootCandidates_card_le
#print axioms nonprime_prime_power_representation
#print axioms prime_power_log_window_data
#print axioms nonprimePrimePowerWindow_card_le
#print axioms nonprimeNaturalWindow_eq_zero_outside
#print axioms nonprimeNaturalWindow_mem_le
#print axioms tsum_nonprimeNaturalWindow_le
end RH080Next.Primal
