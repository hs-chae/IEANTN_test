import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open Filter

namespace RankTransport

def p (n : ℕ) : ℕ := Nat.nth Nat.Prime n
def P (n : ℕ) : ℝ := p n
def piReal (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊
def piStrict (x : ℝ) : ℕ := Nat.primeCounting' ⌈x⌉₊
def y (c x : ℝ) : ℝ := x + c * Real.sqrt x * Real.log x
def halfOpenCount (c x : ℝ) : ℕ := piReal (y c x) - piReal x
def normalizedPopulation (c x : ℝ) : ℝ := (halfOpenCount c x : ℝ) / Real.sqrt x
def GoodCoefficient (a c : ℝ) : Prop :=
  0 < c ∧ ∃ δ > 0, ∀ᶠ x in atTop, a + δ ≤ normalizedPopulation c x

def s (n : ℕ) : ℝ := Real.sqrt (P n)
def H (n : ℕ) : ℝ := s n * Real.log (P n)
def rank (n j : ℕ) : ℝ := ((j : ℝ) - 1) / s n
def gap (n j : ℕ) : ℝ := (P (n+j) - P n) / H n

theorem p_mono : StrictMono p := Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem P_mono : StrictMono P := by
  intro i j hij
  change (p i : ℝ) < (p j : ℝ)
  exact_mod_cast p_mono hij

theorem two_le_P (n : ℕ) : 2 ≤ P n := by
  have h : 2 ≤ p n := (Nat.prime_nth_prime n).two_le
  change (2 : ℝ) ≤ (p n : ℝ)
  exact_mod_cast h

theorem tendsto_P : Tendsto P atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  refine eventually_atTop.mpr ⟨⌈b⌉₊, fun n hn => ?_⟩
  have hnp : n ≤ p n := (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n)
  exact Nat.ceil_le.mp (hn.trans hnp)

theorem count'_p_succ (n : ℕ) : Nat.primeCounting' (p n + 1) = n + 1 := by
  rw [Nat.primeCounting', Nat.count_succ]
  have hp : Nat.Prime (p n) := Nat.prime_nth_prime n
  have hn : Nat.count Nat.Prime (p n) = n := Nat.primeCounting'_nth_eq n
  simp [hp, hn]

theorem pi_P (n : ℕ) : piReal (P n) = n + 1 := by
  simpa only [piReal, P, Nat.floor_natCast, Nat.primeCounting_eq_primeCounting'_succ]
    using count'_p_succ n

theorem count'_gt_index_iff (k m : ℕ) : k < Nat.primeCounting' m ↔ p k < m := by
  have hk : Nat.primeCounting' (p k) = k := Nat.primeCounting'_nth_eq k
  constructor
  · intro h
    by_contra! hm
    have hb := Nat.monotone_primeCounting' hm
    omega
  · intro h
    have hb := Nat.monotone_primeCounting' (Nat.succ_le_of_lt h)
    rw [count'_p_succ] at hb
    omega

theorem pi_rank_iff (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    k < piReal z ↔ P k ≤ z := by
  rw [piReal, Nat.primeCounting_eq_primeCounting'_succ, count'_gt_index_iff]
  exact Nat.lt_succ_iff.trans (Nat.le_floor_iff hz)

theorem piStrict_rank_iff (k : ℕ) (z : ℝ) :
    k < piStrict z ↔ P k < z := by
  rw [piStrict, count'_gt_index_iff]
  exact Nat.lt_ceil

def endpointDefect (z : ℝ) : ℕ :=
  if z = (⌊z⌋₊ : ℝ) ∧ Nat.Prime ⌊z⌋₊ then 1 else 0

theorem pi_endpoint (z : ℝ) (hz : 0 ≤ z) :
    piReal z = piStrict z + endpointDefect z := by
  let m : ℕ := ⌊z⌋₊
  have hge : (m : ℝ) ≤ z := Nat.floor_le hz
  by_cases h : z = (m : ℝ)
  · have hc : ⌈z⌉₊ = m := le_antisymm (Nat.ceil_le.mpr h.le)
      (by exact_mod_cast hge.trans (Nat.le_ceil z))
    unfold piReal piStrict endpointDefect
    change Nat.primeCounting m =
      Nat.primeCounting' ⌈z⌉₊ + (if z = (m : ℝ) ∧ Nat.Prime m then 1 else 0)
    rw [hc, Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting', Nat.count_succ]
    simp [h]
  · have hlt : (m : ℝ) < z := lt_of_le_of_ne hge (Ne.symm h)
    have hc : ⌈z⌉₊ = m+1 :=
      le_antisymm (Nat.ceil_le.mpr (by push_cast; exact (Nat.lt_floor_add_one z).le))
        (Nat.lt_ceil.mpr hlt)
    unfold piReal piStrict endpointDefect
    change Nat.primeCounting m =
      Nat.primeCounting' ⌈z⌉₊ + (if z = (m : ℝ) ∧ Nat.Prime m then 1 else 0)
    simp [h, hc, Nat.primeCounting_eq_primeCounting'_succ]

theorem open_count_defect (n : ℕ) {z : ℝ} (hz : P n < z) :
    piStrict z - piReal (P n) = (piReal z - piReal (P n)) - endpointDefect z := by
  have hz0 : 0 ≤ z := by have := two_le_P n; linarith
  have h := pi_endpoint z hz0
  omega

theorem halfClosed_iff (n j : ℕ) {z : ℝ} (hz : P n ≤ z) (hj : 1 ≤ j) :
    j ≤ piReal z - piReal (P n) ↔ P (n+j) ≤ z := by
  rw [pi_P, ← pi_rank_iff (n+j) ((by have := two_le_P n; linarith : 0 ≤ P n).trans hz)]
  omega

theorem strictOpen_iff (n j : ℕ) (z : ℝ) (hj : 1 ≤ j) :
    j ≤ piStrict z - piReal (P n) ↔ P (n+j) < z := by
  rw [pi_P, ← piStrict_rank_iff (n+j)]
  omega

theorem extra_count_gives_strict (n j : ℕ) {z : ℝ} (hz : P n ≤ z)
    (h : j + 1 ≤ piReal z - piReal (P n)) : P (n+j) < z := by
  have hu := (halfClosed_iff n (j+1) hz (by omega)).mp h
  exact (P_mono (show n+j < n+(j+1) by omega)).trans_le hu

theorem s_pos (n : ℕ) : 0 < s n :=
  Real.sqrt_pos.2 (by have := two_le_P n; linarith)

theorem H_pos (n : ℕ) : 0 < H n :=
  mul_pos (s_pos n) (Real.log_pos (by have := two_le_P n; linarith))

theorem rank_le_iff {n j : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    rank n j ≤ a ↔ j ≤ ⌊a * s n⌋₊ + 1 := by
  rw [rank, div_le_iff₀ (s_pos n)]
  have hz : 0 ≤ a * s n := mul_nonneg ha (s_pos n).le
  cases j with
  | zero => simp; linarith
  | succ j =>
    rw [Nat.succ_le_succ_iff, Nat.le_floor_iff hz]
    push_cast
    ring_nf

theorem rank_nonneg {n j : ℕ} (hj : 1 ≤ j) : 0 ≤ rank n j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  exact div_nonneg (sub_nonneg.mpr hj') (s_pos n).le

theorem gap_pos {n j : ℕ} (hj : 1 ≤ j) : 0 < gap n j :=
  div_pos (sub_pos.mpr (P_mono (show n < n+j by omega))) (H_pos n)

theorem good_transport {a c : ℝ} (h : GoodCoefficient a c) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → rank n j ≤ a → gap n j < c := by
  obtain ⟨hc, δ, hδ, hpop⟩ := h
  have hs : ∀ᶠ n : ℕ in atTop, (2/δ)^2 ≤ P n :=
    tendsto_atTop.mp tendsto_P _
  filter_upwards [tendsto_P.eventually hpop, hs] with n hpop hsize
  intro j hj hr
  have hδs : 2 ≤ δ * s n := by
    have hs' : 2 / δ ≤ s n :=
      (Real.le_sqrt (by positivity) (by have := two_le_P n; linarith)).2 hsize
    exact (mul_comm δ (s n)) ▸ (div_le_iff₀ hδ).mp hs'
  have hr' : (j : ℝ) - 1 ≤ a * s n := (div_le_iff₀ (s_pos n)).mp hr
  have hp' : (a + δ) * s n ≤ (halfOpenCount c (P n) : ℝ) :=
    (le_div_iff₀ (s_pos n)).mp hpop
  have hcount' : (j : ℝ) + 1 ≤ (halfOpenCount c (P n) : ℝ) := by
    rw [add_mul] at hp'
    linarith
  have hcount : j + 1 ≤ halfOpenCount c (P n) := by exact_mod_cast hcount'
  have hy : y c (P n) = P n + c * H n := by
    unfold y H s
    ring
  have hyge : P n ≤ y c (P n) := by
    rw [hy]
    linarith [mul_pos hc (H_pos n)]
  have hu := extra_count_gives_strict n j hyge hcount
  rw [hy] at hu
  exact (div_lt_iff₀ (H_pos n)).mpr (by linarith)


-- Finite synchronization: this is not an interchange of two eventual quantifiers.
theorem finite_menu {I : Finset ℕ} {a c : ℕ → ℝ}
    (h : ∀ i ∈ I, GoodCoefficient (a i) (c i)) :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ I, ∀ j : ℕ, 1 ≤ j → rank n j ≤ a i → gap n j < c i :=
  (I.eventually_all).2 (fun i hi => good_transport (h i hi))

theorem affine_transport {b m ρ β ε : ℝ} (hm : 0 ≤ m) (hε : 0 < ε)
    (hcurve : ∀ a : ℝ, 0 ≤ a → GoodCoefficient a (b + m*a + ρ)) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → rank n j ≤ β →
      gap n j < b + m * rank n j + ρ + ε := by
  let d : ℝ := ε / (m+1)
  have hd : 0 < d := div_pos hε (by linarith)
  let a : ℕ → ℝ := fun i => i*d
  let c : ℕ → ℝ := fun i => b + m*(a i) + ρ
  let I : Finset ℕ := Finset.range (⌈β / d⌉₊ + 1)
  have hmε : m*d ≤ ε := by
    have hh : d * (m+1) = ε := div_mul_cancel₀ ε (by linarith)
    nlinarith
  have he : ∀ᶠ n : ℕ in atTop, ∀ i ∈ I, ∀ j : ℕ,
      1 ≤ j → rank n j ≤ a i → gap n j < c i :=
    finite_menu (fun i _ => hcurve (a i) (by dsimp [a]; positivity))
  filter_upwards [he] with n hn
  intro j hj hr
  have hr0 : 0 ≤ rank n j := rank_nonneg hj
  let i : ℕ := ⌈rank n j / d⌉₊
  have hiI : i ∈ I := by
    apply Finset.mem_range.mpr (Nat.lt_succ_of_le _)
    exact Nat.ceil_mono (div_le_div_of_nonneg_right hr hd.le)
  have hri : rank n j ≤ a i := by
    exact (div_le_iff₀ hd).mp (Nat.le_ceil _)
  have hil : a i ≤ rank n j + d := by
    have hz : (i : ℝ) ≤ rank n j / d + 1 := by
      cases hi : i with
      | zero => simp; positivity
      | succ k =>
        have hk : (k : ℝ) < rank n j / d := Nat.lt_ceil.mp (by change k < i; rw [hi]; exact Nat.lt_succ_self k)
        push_cast [hi]
        linarith
    dsimp [a]
    calc
      (i : ℝ)*d ≤ (rank n j / d + 1)*d := mul_le_mul_of_nonneg_right hz hd.le
      _ = rank n j + d := by rw [add_mul, div_mul_cancel₀ _ hd.ne', one_mul]
  have hsmall := hn i hiI j hj hri
  have hc : c i ≤ b + m * rank n j + ρ + ε := by
    dsimp [c]
    have hmono := mul_le_mul_of_nonneg_left hil hm
    rw [mul_add] at hmono
    linarith
  exact hsmall.trans_le hc

def q : ℝ := 20582561296 / 24680948495
def gaussian (a : ℝ) : ℝ := q * (1 + 2*a)
def sparse (a : ℝ) : ℝ := 944247/1000000 + (1163388/1000000)*a
def flat (a : ℝ) : ℝ := 9/8 + (16/15)*a
def envelope (a : ℝ) : ℝ := min (gaussian a) (min (sparse a) (flat a))
def GaussianCurve : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∀ e : ℝ, 0 < e → GoodCoefficient a (gaussian a + e)
def SparseCurve : Prop := ∀ a : ℝ, 0 ≤ a → GoodCoefficient a (sparse a)
def FlatCurve : Prop := ∀ a : ℝ, 0 ≤ a → GoodCoefficient a (flat a)

theorem growing_rank
    (hG : GaussianCurve) (hS : SparseCurve) (hF : FlatCurve)
    {β η : ℝ} (hβ : 0 ≤ β) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ ⌊β * s n⌋₊ + 1 →
       0 < gap n j ∧
       gap n j < min (envelope (rank n j) + η)
         (min (gaussian β + η) (min (sparse β) (flat β))) := by
  have g := affine_transport (β := β) (b := q) (m := 2*q) (ρ := η/2)
    (by unfold q; norm_num) (show 0 < η/2 by positivity) fun a ha => by
      convert hG a ha (η/2) (by positivity) using 1
      unfold gaussian
      ring
  have b := affine_transport (β := β) (b := 944247/1000000) (m := 1163388/1000000) (ρ := 0)
    (by norm_num) hη fun a ha => by simpa [sparse] using hS a ha
  have f := affine_transport (β := β) (b := 9/8) (m := 16/15) (ρ := 0)
    (by norm_num) hη fun a ha => by simpa [flat] using hF a ha
  filter_upwards [g, b, f, good_transport (hG β hβ η hη),
    good_transport (hS β hβ), good_transport (hF β hβ)] with n hg hb hf hgb hbb hfb
  intro j hj hjβ
  have hr := (rank_le_iff hβ).mpr hjβ
  refine ⟨gap_pos hj, lt_min_iff.mpr ⟨?_, ?_⟩⟩
  · have hg' : gap n j < gaussian (rank n j) + η := by
      convert hg j hj hr using 1
      unfold gaussian
      ring
    have hb' : gap n j < sparse (rank n j) + η := by simpa [sparse] using hb j hj hr
    have hf' : gap n j < flat (rank n j) + η := by simpa [flat] using hf j hj hr
    rcases min_choice (sparse (rank n j)) (flat (rank n j)) with h | h
    · rw [envelope, h]
      rcases min_choice (gaussian (rank n j)) (sparse (rank n j)) with h | h <;>
        rw [h] <;> assumption
    · rw [envelope, h]
      rcases min_choice (gaussian (rank n j)) (flat (rank n j)) with h | h <;>
        rw [h] <;> assumption
  · exact lt_min_iff.mpr ⟨hgb j hj hr, lt_min_iff.mpr ⟨hbb j hj hr, hfb j hj hr⟩⟩


def MarginInput (D B U : ℝ) : Prop :=
  ∀ a c : ℝ, 0 < c → a < (c*D-B)/(2*U) → GoodCoefficient a c

theorem margin_transport {D B U β e : ℝ}
    (hD : 0 < D) (hB : 0 ≤ B) (hU : 0 < U) (he : 0 < e)
    (hM : MarginInput D B U) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → rank n j ≤ β →
      gap n j < B/D + (2*U/D)*rank n j + e := by
  have hSlope : 0 ≤ 2*U/D := by positivity
  have haff := affine_transport (β := β) (ρ := e/2) (b := B/D)
    hSlope (show 0 < e/2 by positivity) ?_
  · filter_upwards [haff] with n hn
    intro j hj hr
    linarith [hn j hj hr]
  · intro a ha
    let c := B/D + (2*U/D)*a + e/2
    have hc : 0 < c := by dsimp [c]; positivity
    apply hM a c hc
    apply (lt_div_iff₀ (by positivity : 0 < 2*U)).mpr
    have hcalc : c*D-B = a*(2*U) + e/2*D := by
      dsimp [c]
      field_simp
      ring
    rw [hcalc]
    have : 0 < e/2*D := by positivity
    linarith

def ds : ℝ := 1 - 4*(119725872611533800/(8*10^18))
def bs : ℝ := 887721072633027910/10^18
def us : ℝ := 546871713113309800/10^18
def df : ℝ := (15*533333333333333333)/(8*10^18)
def bf : ℝ := 1120475208606944546/10^18
def uf : ℝ := 533333333333333333/10^18

theorem refined_rank (hG : GaussianCurve) (hS : MarginInput ds bs us)
    (hF : MarginInput df bf uf) {β eg es ef : ℝ}
    (hβ : 0 ≤ β) (hg : 0 < eg) (hs : 0 < es) (hf : 0 < ef) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ ⌊β*s n⌋₊ + 1 →
      0 < gap n j ∧ gap n j <
        min (gaussian (rank n j) + eg)
          (min (bs/ds + (2*us/ds)*rank n j + min es (1/2000000))
             (bf/df + (2*uf/df)*rank n j + min ef (1/250))) := by
  have g := affine_transport (β := β) (b := q) (m := 2*q) (ρ := eg/2)
    (by unfold q; norm_num) (show 0 < eg/2 by positivity) fun a ha => by
      convert hG a ha (eg/2) (by positivity) using 1
      unfold gaussian
      ring
  have hsm : 0 < min es (1/2000000) := lt_min_iff.mpr ⟨hs, by norm_num⟩
  have hfm : 0 < min ef (1/250) := lt_min_iff.mpr ⟨hf, by norm_num⟩
  have b := margin_transport (β := β) (by norm_num [ds]) (by norm_num [bs])
    (by norm_num [us]) hsm hS
  have f := margin_transport (β := β) (by norm_num [df]) (by norm_num [bf])
    (by norm_num [uf]) hfm hF
  filter_upwards [g, b, f] with n hgn hbn hfn
  intro j hj hjβ
  have hr := (rank_le_iff hβ).mpr hjβ
  refine ⟨gap_pos hj, lt_min_iff.mpr ⟨?_, lt_min_iff.mpr ⟨hbn j hj hr, hfn j hj hr⟩⟩⟩
  calc
    gap n j < q + (2*q)*rank n j + eg/2 + eg/2 := hgn j hj hr
    _ = gaussian (rank n j) + eg := by unfold gaussian; ring

theorem refined_sparse_lt {r : ℝ} (hr : 0 ≤ r) :
    bs/ds + (2*us/ds)*r + 1/2000000 < sparse r := by
  have hs : 2*us/ds ≤ (1163388/1000000 : ℝ) := by norm_num [ds, us]
  have hb : bs/ds + 1/2000000 < (944247/1000000 : ℝ) := by norm_num [ds, bs]
  unfold sparse
  linarith [mul_le_mul_of_nonneg_right hs hr]

theorem refined_flat_lt (r : ℝ) :
    bf/df + (2*uf/df)*r + 1/250 < flat r := by
  have hs : 2*uf/df = (16/15 : ℝ) := by norm_num [df, uf]
  have hb : bf/df + 1/250 < (9/8 : ℝ) := by norm_num [df, bf]
  unfold flat
  rw [hs]
  linarith

end RankTransport

#print axioms RankTransport.pi_endpoint
#print axioms RankTransport.growing_rank
#print axioms RankTransport.refined_rank
