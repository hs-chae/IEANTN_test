import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open Filter
open scoped Topology
namespace RankTransport
noncomputable section

noncomputable def p (n : ℕ) : ℝ := (Nat.nth Nat.Prime n : ℝ)
noncomputable def H (x : ℝ) : ℝ := Real.sqrt x * Real.log x
noncomputable def piLE (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊
noncomputable def piLT (x : ℝ) : ℕ := Nat.primeCounting' ⌈x⌉₊
noncomputable def count (c x : ℝ) : ℕ := piLE (x + c * H x) - piLE x
def Good (a c : ℝ) : Prop :=
  0 < c ∧ ∃ d > 0, ∀ᶠ x : ℝ in atTop, a + d ≤ (count c x : ℝ) / Real.sqrt x

theorem p_strict : StrictMono p := fun _ _ h => by
  unfold p
  exact_mod_cast (Nat.nth_strictMono Nat.infinite_setOfPred_prime h)

theorem p_ge (n : ℕ) : (n : ℝ) + 2 ≤ p n := by
  unfold p
  exact_mod_cast Nat.add_two_le_nth_prime n

theorem p_tendsto : Tendsto p atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  obtain ⟨k, hk⟩ := exists_nat_ge b
  filter_upwards [eventually_ge_atTop k] with n hn
  have : (k : ℝ) ≤ n := by exact_mod_cast hn
  linarith [p_ge n]

theorem p_pos (n : ℕ) : 0 < p n := by linarith [p_ge n, Nat.cast_nonneg (α := ℝ) n]
theorem H_pos (n : ℕ) : 0 < H (p n) := by
  apply mul_pos (Real.sqrt_pos.2 (p_pos n)) (Real.log_pos ?_)
  linarith [p_ge n, Nat.cast_nonneg (α := ℝ) n]

theorem rank_lt_piLT (k : ℕ) (y : ℝ) : k < piLT y ↔ p k < y := by
  rw [piLT, Nat.primeCounting', ← not_le, Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime,
    not_le, Nat.lt_ceil]
  rfl

theorem rank_lt_piLE (k : ℕ) {y : ℝ} (hy : 0 ≤ y) : k < piLE y ↔ p k ≤ y := by
  rw [piLE, Nat.primeCounting, Nat.primeCounting', ← not_le,
    Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime, not_le, Nat.lt_succ_iff,
    Nat.le_floor_iff hy]
  rfl

theorem piLE_p (n : ℕ) : piLE (p n) = n + 1 := by
  have h1 := (rank_lt_piLE n (p_pos n).le).2 le_rfl
  have h2 : ¬ n + 1 < piLE (p n) := by
    rw [rank_lt_piLE _ (p_pos n).le]
    exact not_le_of_gt (p_strict (Nat.lt_succ_self n))
  omega

theorem halfOpen_bridge (n j : ℕ) {y : ℝ} (hy : p n ≤ y) (hj : 0 < j) :
    j ≤ piLE y - piLE (p n) ↔ p (n+j) ≤ y := by
  rw [← rank_lt_piLE _ ((p_pos n).le.trans hy), piLE_p]
  omega

theorem open_bridge (n j : ℕ) (y : ℝ) (hj : 0 < j) :
    j ≤ piLT y - piLE (p n) ↔ p (n+j) < y := by
  rw [← rank_lt_piLT, piLE_p]
  omega

theorem spare_prime (n j : ℕ) {y : ℝ} (hy : p n ≤ y)
    (h : j+1 ≤ piLE y - piLE (p n)) : p (n+j) < y := by
  have h' := (halfOpen_bridge n (j+1) hy (by omega)).1 h
  exact (p_strict (by omega : n+j < n+(j+1))).trans_le h'

theorem sqrt_p_tendsto : Tendsto (fun n => Real.sqrt (p n)) atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  filter_upwards [p_tendsto.eventually (eventually_ge_atTop (b*b))] with n hn
  exact le_trans (le_abs_self b) (by rw [← Real.sqrt_mul_self_eq_abs]; exact Real.sqrt_le_sqrt hn)

theorem eventually_spare {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ d * Real.sqrt (p n) := by
  filter_upwards [sqrt_p_tendsto.eventually (eventually_ge_atTop (2/d))] with n hn
  rw [mul_comm]
  exact (div_le_iff₀ hd).1 hn

theorem anchor {a c : ℝ} (ha : Good a c) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 0 < j →
      ((j : ℝ)-1) / Real.sqrt (p n) ≤ a →
      0 < p (n+j)-p n ∧ p (n+j)-p n < c * H (p n) := by
  rcases ha with ⟨hc, d, hd, hev⟩
  filter_upwards [p_tendsto.eventually hev, eventually_spare hd] with n hn hs j hj hj'
  have hp := Real.sqrt_pos.2 (p_pos n)
  have hj'' := (div_le_iff₀ hp).1 hj'
  have hn' := (le_div_iff₀ hp).1 hn
  have hN : j+1 ≤ count c (p n) := by
    have : (j : ℝ)+1 ≤ (count c (p n) : ℝ) := by linarith [mul_add (Real.sqrt (p n)) a d, add_mul a d (Real.sqrt (p n))]
    exact_mod_cast this
  constructor
  · exact sub_pos.2 (p_strict (by omega))
  · have h := spare_prime n j (le_add_of_nonneg_right (mul_nonneg hc.le (H_pos n).le)) hN
    linarith

theorem normRank_mem (n j : ℕ) {b : ℝ} (hb : 0 ≤ b) (hj : 0 < j)
    (hj' : j ≤ ⌊b * Real.sqrt (p n)⌋₊ + 1) :
    ((j : ℝ)-1) / Real.sqrt (p n) ∈ Set.Icc 0 b := by
  have hs := Real.sqrt_pos.2 (p_pos n)
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h2 : j-1 ≤ ⌊b * Real.sqrt (p n)⌋₊ := by omega
  have h3 : ((j-1 : ℕ) : ℝ) ≤ (⌊b * Real.sqrt (p n)⌋₊ : ℝ) := by exact_mod_cast h2
  rw [Nat.cast_sub hj] at h3
  simp only [Nat.cast_one] at h3
  exact ⟨div_nonneg (sub_nonneg.2 h1) hs.le,
    (div_le_iff₀ hs).2 (h3.trans (Nat.floor_le (mul_nonneg hb hs.le)))⟩

/-- Uniform transfer from local width certificates, using compactness of the rank range. -/
theorem uniform_of_local {b : ℝ} (hb : 0 ≤ b) {w : ℝ → ℝ} (hw : Continuous w)
    (loc : ∀ r ∈ Set.Icc 0 b, ∃ a c : ℝ, r < a ∧ c < w r ∧ Good a c) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 0 < j → j ≤ ⌊b * Real.sqrt (p n)⌋₊ + 1 →
      0 < p (n+j)-p n ∧
      p (n+j)-p n < w (((j : ℝ)-1)/Real.sqrt (p n)) * H (p n) := by
  classical
  let ι := { ac : ℝ × ℝ // Good ac.1 ac.2 }
  let U (i : ι) : Set ℝ := { r | r < i.val.1 ∧ i.val.2 < w r }
  have hU (i : ι) : IsOpen (U i) :=
    (isOpen_lt continuous_id continuous_const).inter (isOpen_lt continuous_const hw)
  have hcov : Set.Icc 0 b ⊆ ⋃ i, U i := by
    intro r hr
    obtain ⟨a,c,ha,hc,hg⟩ := loc r hr
    exact Set.mem_iUnion.2 ⟨⟨(a,c),hg⟩, ha,hc⟩
  obtain ⟨I, hI⟩ := isCompact_Icc.elim_finite_subcover U hU hcov
  have hev := (Filter.eventually_all_finset I).2 (fun i _ => anchor i.property)
  filter_upwards [hev] with n hn j hj hjb
  let r := ((j : ℝ)-1)/Real.sqrt (p n)
  have hr : r ∈ Set.Icc 0 b := normRank_mem n j hb hj hjb
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hI hr)
  obtain ⟨hiI, hiU⟩ := Set.mem_iUnion.1 hi
  change r < i.val.1 ∧ i.val.2 < w r at hiU
  obtain ⟨hp, hlt⟩ := hn i hiI j hj hiU.1.le
  exact ⟨hp, hlt.trans (mul_lt_mul_of_pos_right hiU.2 (H_pos n))⟩

/-- A continuous leading curve with arbitrarily small pointwise positive width slack. -/
theorem uniform_of_curve {b : ℝ} (hb : 0 ≤ b) {f : ℝ → ℝ} (hf : Continuous f)
    (curve : ∀ a ≥ 0, ∀ e > 0, Good a (f a + e)) {e : ℝ} (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 0 < j → j ≤ ⌊b * Real.sqrt (p n)⌋₊ + 1 →
      0 < p (n+j)-p n ∧
      p (n+j)-p n < (f (((j : ℝ)-1)/Real.sqrt (p n)) + e) * H (p n) := by
  apply uniform_of_local hb (hf.add continuous_const)
  intro r hr
  obtain ⟨d, hd, hfd⟩ := Metric.continuousAt_iff.1 (hf.continuousAt (x := r)) (e/2) (by positivity)
  let a := r + d/2
  have hda : dist a r < d := by
    dsimp [a]
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity : 0 < d/2)]
    linarith
  have hfa := hfd hda
  rw [Real.dist_eq, abs_lt] at hfa
  have hra : r < a := by dsimp [a]; linarith
  exact ⟨a, f a+e/2, hra, by change f a + e/2 < f r + e; linarith [hfa.2], curve a (hr.1.trans hra.le) (e/2) (by positivity)⟩

theorem piLE_mono : Monotone piLE :=
  Nat.monotone_primeCounting.comp Nat.floor_mono

theorem count_mono (n : ℕ) {c d : ℝ} (h : c ≤ d) : count c (p n) ≤ count d (p n) := by
  apply Nat.sub_le_sub_right
  apply piLE_mono
  exact add_le_add_right (mul_le_mul_of_nonneg_right h (H_pos n).le) _

theorem anchor_min {a c d : ℝ} (hc : Good a c) (hd : Good a d) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 0 < j →
      ((j : ℝ)-1) / Real.sqrt (p n) ≤ a →
      0 < p (n+j)-p n ∧ p (n+j)-p n < min c d * H (p n) := by
  filter_upwards [anchor hc, anchor hd] with n hn hn' j hj hj'
  rcases le_total c d with h|h
  · simpa only [min_eq_left h] using hn j hj hj'
  · simpa only [min_eq_right h] using hn' j hj hj'

def q : ℝ := 20582561296/24680948495
def g (a : ℝ) : ℝ := q*(1+2*a)
def sparse (a : ℝ) : ℝ := 944247/1000000 + (1163388/1000000)*a
def flat (a : ℝ) : ℝ := 9/8 + (16/15)*a
def frontier (a : ℝ) : ℝ := min (g a) (min (sparse a) (flat a))

def GaussianCurve : Prop := ∀ a ≥ 0, ∀ e > 0, Good a (g a+e)
def SparseCurve : Prop := ∀ a ≥ 0, Good a (sparse a)
def FlatCurve : Prop := ∀ a ≥ 0, Good a (flat a)

theorem continuous_g : Continuous g := by unfold g; fun_prop
theorem continuous_sparse : Continuous sparse := by unfold sparse; fun_prop
theorem continuous_flat : Continuous flat := by unfold flat; fun_prop
theorem continuous_frontier : Continuous frontier :=
  continuous_g.min (continuous_sparse.min continuous_flat)

theorem H_eventually_pos : ∀ᶠ x : ℝ in atTop, 0 < H x := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  exact mul_pos (Real.sqrt_pos.2 (by linarith)) (Real.log_pos (by linarith))

theorem good_mono_width {a c d : ℝ} (h : Good a c) (hcd : c ≤ d) : Good a d := by
  rcases h with ⟨hc,m,hm,hev⟩
  refine ⟨hc.trans_le hcd, m, hm, ?_⟩
  filter_upwards [hev, H_eventually_pos] with x hx hH
  have hN : count c x ≤ count d x := by
    apply Nat.sub_le_sub_right
    apply piLE_mono
    exact add_le_add_right (mul_le_mul_of_nonneg_right hcd hH.le) _
  exact hx.trans (div_le_div_of_nonneg_right (by exact_mod_cast hN) (Real.sqrt_nonneg x))

theorem good_min {a c d : ℝ} (h₁ : Good a c) (h₂ : Good a d) : Good a (min c d) := by
  rcases le_total c d with h|h
  · simpa only [min_eq_left h] using h₁
  · simpa only [min_eq_right h] using h₂

theorem uniform_packet (hg : GaussianCurve) (hs : SparseCurve) (hf : FlatCurve)
    {b e : ℝ} (hb : 0 ≤ b) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 0 < j → j ≤ ⌊b * Real.sqrt (p n)⌋₊ + 1 →
      0 < p (n+j)-p n ∧
      p (n+j)-p n < (frontier (((j : ℝ)-1)/Real.sqrt (p n)) + e) * H (p n) := by
  apply uniform_of_curve hb continuous_frontier _ he
  intro a ha t ht
  have h := good_min (hg a ha t ht) (good_min
    (good_mono_width (hs a ha) (by linarith : sparse a ≤ sparse a+t))
    (good_mono_width (hf a ha) (by linarith : flat a ≤ flat a+t)))
  simpa only [frontier, min_add_add_right] using h

theorem uniform_fixed_cap (hg : GaussianCurve) (hs : SparseCurve) (hf : FlatCurve)
    {b e : ℝ} (hb : 0 ≤ b) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 0 < j → j ≤ ⌊b * Real.sqrt (p n)⌋₊ + 1 →
      0 < p (n+j)-p n ∧ p (n+j)-p n < min (g b+e) (min (sparse b) (flat b)) * H (p n) := by
  filter_upwards [anchor (good_min (hg b hb e he) (good_min (hs b hb) (hf b hb)))] with n hn j hj hjb
  exact hn j hj (normRank_mem n j hb hj hjb).2


/-- Closed-end counting differs by exactly the possible upper endpoint. -/
theorem piLT_eq_piLE_sub_endpoint {y : ℝ} (hy : 0 ≤ y) :
    piLT y = piLE y - (if (⌊y⌋₊ : ℝ) = y ∧ Nat.Prime ⌊y⌋₊ then 1 else 0) := by
  classical
  have hfl := Nat.floor_le hy
  have hlt := Nat.lt_floor_add_one y
  by_cases h : (⌊y⌋₊ : ℝ) = y
  · have hc : ⌈y⌉₊ = ⌊y⌋₊ := by conv_lhs => rw [← h]; simp
    rw [piLT, hc, piLE, Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
    by_cases hp : Nat.Prime ⌊y⌋₊ <;> simp [h, hp]
  · have hc : ⌈y⌉₊ = ⌊y⌋₊ + 1 := by
      apply le_antisymm
      · apply Nat.ceil_le.2
        push_cast
        exact hlt.le
      · exact Nat.succ_le_of_lt (Nat.lt_ceil.2 (lt_of_le_of_ne hfl h))
    simp [piLT, hc, piLE, Nat.primeCounting, h]

theorem open_eq_halfOpen_sub_endpoint (n : ℕ) {y : ℝ} (hy : p n ≤ y) :
    piLT y - piLE (p n) =
    (piLE y - piLE (p n)) - (if (⌊y⌋₊ : ℝ) = y ∧ Nat.Prime ⌊y⌋₊ then 1 else 0) := by
  rw [piLT_eq_piLE_sub_endpoint ((p_pos n).le.trans hy)]
  omega

def errorQ (x : ℝ) : ℝ := Real.log (Real.log x) / Real.log x + 2*(Real.log x / Real.sqrt x)

theorem errorQ_tendsto : Tendsto errorQ atTop (𝓝 0) := by
  have h₁ := (isLittleO_log_rpow_atTop (r := 1) zero_lt_one).tendsto_div_nhds_zero
  simp only [Real.rpow_one] at h₁
  have h₂ := (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).tendsto_div_nhds_zero
  simp only [← Real.sqrt_eq_rpow] at h₂
  have h₃ : Tendsto (fun x : ℝ => (2 : ℝ) * (Real.log x / Real.sqrt x)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul h₂ (a := (2 : ℝ))
  unfold errorQ
  simpa only [Function.comp_apply, add_zero] using (h₁.comp Real.tendsto_log_atTop).add h₃

/-- One fixed-window output of the named BR analytic predicate, after inserting
    the positive denominator and the attained positive maximum. The mass can
    already be replaced by an upper bound. No uniformity in the coefficient c. -/
def BRLower (A D K : ℝ) : Prop :=
  ∀ c > 0, ∃ C ≥ 0, ∀ᶠ x : ℝ in atTop,
    (c*D-A)/K-C*errorQ x ≤ (count c x : ℝ)/Real.sqrt x

theorem BR_line {A D K : ℝ} (hA : 0 ≤ A) (hD : 0 < D) (hK : 0 < K)
    (hBR : BRLower A D K) {r e : ℝ} (hr : 0 ≤ r) (he : 0 < e) :
    Good r ((A+K*r)/D+e) := by
  let c := (A+K*r)/D+e
  have hc : 0 < c := add_pos_of_nonneg_of_pos (div_nonneg (by positivity) hD.le) he
  obtain ⟨C, _, hC⟩ := hBR c hc
  have hmul : Tendsto (fun x => C * errorQ x) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul errorQ_tendsto (a := C)
  have hd : 0 < e*D/K/2 := by positivity
  refine ⟨hc, e*D/K/2, hd, ?_⟩
  filter_upwards [hC, hmul.eventually_lt_const hd] with x hx hcx
  have hident : (c*D-A)/K = r+e*D/K := by
    dsimp [c]
    field_simp
    ring
  rw [hident] at hx
  linarith

def As : ℝ := 887721072633027910/1000000000000000000
def Ds : ℝ := 9401370636942331/10000000000000000
def Ks : ℝ := 1093743426226619600/1000000000000000000
def Af : ℝ := 1120475208606944546/1000000000000000000
def Df : ℝ := 1599999999999999999/1600000000000000000
def Kf : ℝ := 1066666666666666666/1000000000000000000
def sparseStar (r : ℝ) : ℝ := (As+Ks*r)/Ds
def flatStar (r : ℝ) : ℝ := (Af+Kf*r)/Df
def SharpSparse : Prop := BRLower As Ds Ks
def SharpFlat : Prop := BRLower Af Df Kf

theorem sparseStar_good (hs : SharpSparse) {r e : ℝ} (hr : 0 ≤ r) (he : 0 < e) :
    Good r (sparseStar r+e) :=
  BR_line (by norm_num [As]) (by norm_num [Ds]) (by norm_num [Ks]) hs hr he

theorem flatStar_good (hf : SharpFlat) {r e : ℝ} (hr : 0 ≤ r) (he : 0 < e) :
    Good r (flatStar r+e) :=
  BR_line (by norm_num [Af]) (by norm_num [Df]) (by norm_num [Kf]) hf hr he

theorem continuous_sparseStar : Continuous sparseStar := by unfold sparseStar; fun_prop
theorem continuous_flatStar : Continuous flatStar := by unfold flatStar; fun_prop

def sharpFrontier (r : ℝ) : ℝ := min (g r) (min (sparseStar r) (flatStar r))

theorem uniform_sharp (hg : GaussianCurve) (hs : SharpSparse) (hf : SharpFlat)
    {b eG eS eF : ℝ} (hb : 0 ≤ b) (hG : 0 < eG) (hS : 0 < eS) (hF : 0 < eF) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 0 < j → j ≤ ⌊b * Real.sqrt (p n)⌋₊ + 1 →
      let r := ((j : ℝ)-1)/Real.sqrt (p n)
      0 < p (n+j)-p n ∧ p (n+j)-p n <
        min (g r+eG) (min (sparseStar r+eS) (flatStar r+eF)) * H (p n) := by
  have uG := uniform_of_curve hb continuous_g hg hG
  have uS := uniform_of_curve hb continuous_sparseStar (fun _ hr _ he => sparseStar_good hs hr he) hS
  have uF := uniform_of_curve hb continuous_flatStar (fun _ hr _ he => flatStar_good hf hr he) hF
  filter_upwards [uG, uS, uF] with n hnG hnS hnF j hj hjb
  dsimp
  rw [min_mul_of_nonneg _ _ (H_pos n).le, min_mul_of_nonneg _ _ (H_pos n).le]
  exact ⟨(hnG j hj hjb).1, lt_min ((hnG j hj hjb).2) (lt_min ((hnS j hj hjb).2) ((hnF j hj hjb).2))⟩

theorem explicit_savings {r : ℝ} (hr : 0 ≤ r) :
    sparseStar r+1/2000000 ≤ sparse r ∧ flatStar r+1/250 ≤ flat r := by
  constructor <;>
    norm_num [sparseStar, flatStar, As, Ks, Ds, Af, Kf, Df, sparse, flat, add_div, mul_div_assoc] <;>
    linarith

end
end RankTransport

#print axioms RankTransport.open_eq_halfOpen_sub_endpoint
#print axioms RankTransport.uniform_packet
#print axioms RankTransport.uniform_fixed_cap
#print axioms RankTransport.uniform_sharp
#print axioms RankTransport.explicit_savings
