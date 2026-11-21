import PrimeSieveExec
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.Sort
import Mathlib.Tactic
import Std.Data.HashMap.Lemmas

/-! Quotient sieve: exact mathematical survivor recurrence, and program below. -/
namespace LocalPrimeSieve
open Finset

def good (p n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter (fun v => v.Prime ∨ p ≤ v.minFac)

def S (p n : ℕ) : ℕ := (good p n).card

theorem mem_good {p n v : ℕ} :
    v ∈ good p n ↔ 2 ≤ v ∧ v ≤ n ∧ (v.Prime ∨ p ≤ v.minFac) := by
  simp [good, and_assoc]

theorem good_mono_right (p : ℕ) {a b : ℕ} (h : a ≤ b) :
    good p a ⊆ good p b := fun _ hx => by
  rcases mem_good.mp hx with ⟨h₁,h₂,h₃⟩
  exact mem_good.mpr ⟨h₁,h₂.trans h,h₃⟩

theorem good_anti_left (n : ℕ) {p q : ℕ} (h : p ≤ q) :
    good q n ⊆ good p n := fun _ hx => by
  rcases mem_good.mp hx with ⟨h₁,h₂,h₃⟩
  exact mem_good.mpr ⟨h₁,h₂,h₃.imp id (le_trans h)⟩

theorem S_initial (n : ℕ) : S 2 n = n-1 := by
  have he : good 2 n = Finset.Icc 2 n := by
    ext v
    rw [mem_good, mem_Icc]
    constructor
    · tauto
    · rintro ⟨hv, hn⟩
      exact ⟨hv,hn,Or.inr (Nat.minFac_prime (by omega)).two_le⟩
  simp [S, he, Nat.card_Icc]

def removed (p n : ℕ) : Finset ℕ := good p n \ good (p+1) n

theorem mem_removed {p n v : ℕ} :
    v ∈ removed p n ↔ 2 ≤ v ∧ v ≤ n ∧ ¬v.Prime ∧ v.minFac = p := by
  unfold removed
  rw [Finset.mem_sdiff, mem_good, mem_good]
  constructor
  · rintro ⟨⟨hv,hn,hpre⟩,hpost⟩
    have hnp : ¬v.Prime := fun hvp => hpost ⟨hv,hn,Or.inl hvp⟩
    have hle : p ≤ v.minFac := hpre.resolve_left hnp
    have hlt : ¬p+1 ≤ v.minFac := fun hh => hpost ⟨hv,hn,Or.inr hh⟩
    exact ⟨hv,hn,hnp,by omega⟩
  · rintro ⟨hv,hn,hnp,he⟩
    refine ⟨⟨hv,hn,Or.inr he.ge⟩, ?_⟩
    rintro ⟨_,_,hg⟩
    exact hg.elim hnp (by omega)

theorem S_same {p n : ℕ} (h : ¬p.Prime ∨ n < p*p) : S (p+1) n = S p n := by
  have he : good (p+1) n = good p n := by
    apply Finset.Subset.antisymm (good_anti_left n (by omega))
    intro v hv
    by_contra hv'
    obtain ⟨h₂,hn,hvnp,he⟩ := mem_removed.mp (Finset.mem_sdiff.mpr ⟨hv,hv'⟩)
    rcases h with h | h
    · exact h (he ▸ Nat.minFac_prime (by omega))
    · have hh := Nat.minFac_sq_le_self (by omega : 0 < v) hvnp
      rw [he, pow_two] at hh
      omega
  simp [S,he]

def factors (p n : ℕ) : Finset ℕ := (Finset.Icc p (n/p)).filter (fun q => p ≤ q.minFac)

theorem mem_factors {p n q : ℕ} :
    q ∈ factors p n ↔ p ≤ q ∧ q ≤ n/p ∧ p ≤ q.minFac := by
  simp [factors, and_assoc]

theorem factors_eq {p n : ℕ} (hp : 2 ≤ p) :
    factors p n = good p (n/p) \ good p (p-1) := by
  ext q
  rw [mem_factors, Finset.mem_sdiff, mem_good, mem_good]
  constructor
  · rintro ⟨h₁,h₂,h₃⟩
    exact ⟨⟨hp.trans h₁,h₂,Or.inr h₃⟩,by omega⟩
  · rintro ⟨⟨hq,hn,hs⟩,hb⟩
    have h₁ : p ≤ q := by by_contra! hh; exact hb ⟨hq,by omega,hs⟩
    have h₂ : p ≤ q.minFac := hs.elim (fun h => by rwa [h.minFac_eq]) id
    exact ⟨h₁,hn,h₂⟩

theorem removed_card {p n : ℕ} (hp : p.Prime) :
    (removed p n).card = (factors p n).card := by
  have hp0 : 0 < p := hp.pos
  have hp2 := hp.two_le
  have hmul : ∀ v ∈ removed p n, v / p * p = v := by
    intro v hv
    have h := (mem_removed.mp hv).2.2.2
    exact Nat.div_mul_cancel (h ▸ Nat.minFac_dvd v)
  apply Finset.card_bij (fun v _ => v/p)
  · intro v hv
    rcases mem_removed.mp hv with ⟨hv2,hvn,hvnp,he⟩
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < v) hvnp
    rw [he,pow_two] at hsq
    have hm := hmul v hv
    have hq : p ≤ v/p := (Nat.le_div_iff_mul_le hp0).mpr hsq
    have hsub : (v/p).minFac ∣ v := by
      have h' : (v/p).minFac ∣ (v/p)*p :=
        (Nat.minFac_dvd (v/p)).trans (dvd_mul_right (v/p) p)
      rwa [hm] at h'
    have hmin := Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : v/p ≠ 1)).two_le hsub
    rw [he] at hmin
    exact mem_factors.mpr ⟨hq,Nat.div_le_div_right hvn,hmin⟩
  · intro v hv w hw he
    rw [← hmul v hv, ← hmul w hw, he]
  · intro q hq
    rcases mem_factors.mp hq with ⟨hq,hqn,hmin⟩
    have hm : p*q ≤ n := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp0).mp hqn
    have h2 : 2 ≤ p*q := by nlinarith
    have hq2 : 2 ≤ q := hp2.trans hq
    have hnp : ¬(p*q).Prime := by
      intro hc
      have hh := (Nat.dvd_prime hc).mp (dvd_mul_right p q)
      rcases hh with hh | hh
      · omega
      · nlinarith
    have he : (p*q).minFac = p := by
      have hh : (p*q).minFac ≤ p := Nat.minFac_le_of_dvd hp2 (dvd_mul_right p q)
      have hpp := Nat.minFac_prime (by omega : p*q ≠ 1)
      have hmd := hpp.dvd_mul.mp (Nat.minFac_dvd (p*q))
      rcases hmd with h | h
      · exact ((Nat.dvd_prime hp).mp h).resolve_left (by have := hpp.two_le; omega)
      · have hle := Nat.minFac_le_of_dvd hpp.two_le h
        omega
    refine ⟨p*q, mem_removed.mpr ⟨h2,hm,hnp,he⟩, Nat.mul_div_cancel_left q hp0⟩

theorem S_update {p n : ℕ} (hp : p.Prime) (h : p*p ≤ n) :
    S (p+1) n = S p n - (S p (n/p)-S p (p-1)) := by
  have hsub : good p (p-1) ⊆ good p (n/p) := good_mono_right p
    (Nat.sub_le p 1 |>.trans ((Nat.le_div_iff_mul_le hp.pos).mpr h))
  have hcc := Finset.card_sdiff_add_card_eq_card (good_anti_left n (by omega : p ≤ p+1))
  change (removed p n).card + S (p+1) n = S p n at hcc
  rw [removed_card hp, factors_eq hp.two_le, Finset.card_sdiff_of_subset hsub] at hcc
  change S p (n/p)-S p (p-1)+S (p+1) n = S p n at hcc
  omega

theorem prime_test {p : ℕ} (hp : 2 ≤ p) : S p (p-1) < S p p ↔ p.Prime := by
  have htest : p ∈ good p p ↔ p.Prime := by
    rw [mem_good]
    constructor
    · rintro ⟨_,_,hpr | hle⟩
      · exact hpr
      · exact Nat.prime_def_minFac.mpr ⟨hp, le_antisymm (Nat.minFac_le (by omega)) hle⟩
    · intro hh
      exact ⟨hp,le_rfl,Or.inl hh⟩
  have hnot : p ∉ good p (p-1) := by simp only [mem_good]; omega
  have herr : good p p \ good p (p-1) = if p.Prime then {p} else ∅ := by
    ext v
    by_cases h : p.Prime
    · simp only [if_pos h,Finset.mem_singleton,Finset.mem_sdiff]
      constructor
      · rintro ⟨hv,hv'⟩
        rcases mem_good.mp hv with ⟨ha,hb,hc⟩
        by_contra! hh
        exact hv' (mem_good.mpr ⟨ha,by omega,hc⟩)
      · rintro rfl
        exact ⟨htest.mpr h,hnot⟩
    · simp only [if_neg h,Finset.notMem_empty,iff_false,Finset.mem_sdiff]
      rintro ⟨hv,hv'⟩
      rcases mem_good.mp hv with ⟨ha,hb,hc⟩
      by_cases hh : v=p
      · exact h (htest.mp (hh ▸ hv))
      · exact hv' (mem_good.mpr ⟨ha,by omega,hc⟩)
  have hx := Finset.card_sdiff_add_card_eq_card (good_mono_right p (Nat.sub_le p 1))
  rw [herr] at hx
  by_cases h : p.Prime
  · simp [h] at hx
    exact iff_of_true (by unfold S; omega) h
  · simp [h] at hx
    exact iff_of_false (by unfold S; omega) h

theorem S_terminal (n : ℕ) : S (n.sqrt+1) n = n.primeCounting := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  unfold S
  apply congrArg Finset.card
  ext v
  rw [mem_good, Nat.mem_primesLE]
  constructor
  · rintro ⟨hv,hn,h⟩
    refine ⟨hn, ?_⟩
    by_contra hnp
    have hq := Nat.minFac_sq_le_self (by omega : 0 < v) hnp
    rw [pow_two] at hq
    have hle := Nat.le_sqrt.mpr (hq.trans hn)
    have hbig := h.resolve_left hnp
    omega
  · rintro ⟨hn,hp⟩
    exact ⟨hp.two_le,hn,Or.inl hp⟩



/-! Executable sparse table, using the actual Lean/Std HashMap API.
Queries use only keys in the quotient-closed domain. -/

theorem mem_keys {n v : ℕ} : v ∈ keys n ↔
    v ≤ n.sqrt ∨ (n.sqrt < v ∧ ∃ j : ℕ, 0 < j ∧ v = n/j) := by
  unfold keys
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp only [digits, List.mem_append, List.mem_range, List.mem_map]
  constructor
  · rintro (h | ⟨i,hi,rfl⟩)
    · exact Or.inl (by omega)
    · have hj : i+1 ≤ n/(n.sqrt+1) := by omega
      have hk : n.sqrt+1 ≤ n/(i+1) := (Nat.le_div_iff_mul_le (by omega)).mpr
        (by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by omega)).mp hj)
      exact Or.inr ⟨by omega,i+1,by omega,rfl⟩
  · rintro (h | ⟨h, j, hj, he⟩)
    · exact Or.inl (by omega)
    · cases j with
      | zero => omega
      | succ i =>
        have hk : n.sqrt+1 ≤ n/(i+1) := by omega
        have hℓ : i+1 ≤ n/(n.sqrt+1) := (Nat.le_div_iff_mul_le (by omega)).mpr
          (by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by omega)).mp hk)
        exact Or.inr ⟨i,by omega,he.symm⟩

theorem mem_keys_div {n v p : ℕ} (hv : v ∈ keys n) (hp : 0 < p) :
    v/p ∈ keys n := by
  rw [mem_keys] at hv ⊢
  rcases hv with h | ⟨h,j,hj,rfl⟩
  · exact Or.inl ((Nat.div_le_self _ _).trans h)
  · by_cases hk : n/j/p ≤ n.sqrt
    · exact Or.inl hk
    · exact Or.inr ⟨by omega,j*p,Nat.mul_pos hj hp,Nat.div_div_eq_div_mul ..⟩

theorem self_mem_keys (n : ℕ) : n ∈ keys n := by
  rw [mem_keys]
  by_cases h : n ≤ n.sqrt
  · exact Or.inl h
  · exact Or.inr ⟨by omega,1,by omega,by simp⟩

theorem digits_nodup (n : ℕ) : (digits n).Nodup := by
  have hr : n/(n.sqrt+1) ≤ n.sqrt := by
    have hn : n < (n.sqrt+1)*(n.sqrt+1) := by
      by_contra! h
      have := Nat.le_sqrt.mpr h
      omega
    apply Nat.lt_succ_iff.mp
    exact (Nat.div_lt_iff_lt_mul (by omega)).mpr hn
  let f : ℕ → ℕ := fun i => n/(i+1)
  have hbig : ∀ i < n/(n.sqrt+1), n.sqrt+1 ≤ f i := by
    intro i hi
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by omega)).mp
      (show i+1 ≤ n/(n.sqrt+1) by omega)
  have hlt : ∀ {i j : ℕ}, i < j → j < n/(n.sqrt+1) → f j < f i := by
    intro i j hij hj
    apply lt_of_le_of_ne (Nat.div_le_div_left (by omega) (by omega))
    intro he
    have hb := hbig j hj
    have hji : i+1 ≤ f j := by omega
    have hm := Nat.div_mul_le_self n (j+1)
    have hlo := Nat.mul_le_mul_left (f j) (show i+2 ≤ j+1 by omega)
    have huu := Nat.lt_mul_div_succ n (by omega : 0 < i+1)
    change n < (i+1)*(f i+1) at huu
    change f j = f i at he
    rw [← he] at huu
    change f j*(j+1) ≤ n at hm
    nlinarith
  unfold digits
  rw [List.nodup_append]
  refine ⟨List.nodup_range, ?_, ?_⟩
  · apply List.Nodup.map_on
    · intro i hi j hj he
      rw [List.mem_range] at hi hj
      rcases lt_trichotomy i j with h | h | h
      · exact False.elim ((ne_of_gt (hlt h hj)) he)
      · exact h
      · exact False.elim ((ne_of_lt (hlt h hi)) he)
    · exact List.nodup_range
  · intro a ha b hb hab
    subst b
    rw [List.mem_range] at ha
    rcases List.mem_map.mp hb with ⟨i,hi,rfl⟩
    rw [List.mem_range] at hi
    have hbi := hbig i hi
    change n.sqrt+1 ≤ n/(i+1) at hbi
    omega

theorem keys_descending (n : ℕ) : (keys n).Pairwise (fun a b => b<a) := by
  have h₁ : (keys n).Pairwise (fun a b : ℕ => b ≤ a) := by
    simpa [keys] using (List.pairwise_mergeSort' (r:=fun a b : ℕ => b≤a) (digits n))
  have h₂ : (keys n).Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (digits_nodup n)
  apply (List.pairwise_and_iff.mpr ⟨h₁,h₂⟩).imp
  intro a b h
  omega

theorem get_insert (t : Table) (k v j : ℕ) :
    get (t.insert k v) j = if k=j then v else get t j := by
  simp [get, Std.HashMap.getD_insert, beq_iff_eq]

theorem initialise_correct (l : List ℕ) (t : Table) (k : ℕ) :
    get (initialise l t) k = if k ∈ l then k-1 else get t k := by
  induction l generalizing t with
  | nil => simp [initialise]
  | cons v vs ih =>
    rw [initialise, ih, get_insert]
    by_cases hm : k ∈ vs
    · simp [hm]
    · by_cases he : v=k
      · subst v
        simp [hm]
      · simp [hm, he, Ne.symm he]

theorem pass_correct {n p : ℕ} (hp : p.Prime) (hpr : p ≤ n.sqrt)
    (l : List ℕ) (hl : l.Pairwise (fun a b => b<a))
    (hsub : ∀ v ∈ l, v ∈ keys n) (t : Table)
    (ht : ∀ v ∈ l, ∀ w ∈ keys n, w ≤ v → get t w = S p w)
    (k : ℕ) :
    get (pass p l t) k = if k ∈ l then S (p+1) k else get t k := by
  induction l generalizing t with
  | nil => simp [pass]
  | cons v vs ih =>
    have hvr := (List.pairwise_cons.mp hl).1
    simp only [pass]
    by_cases h : p*p ≤ v
    · rw [if_pos h]
      set t' := t.insert v (get t v - (get t (v/p)-get t (p-1))) with he
      have hinit : ∀ v' ∈ vs, ∀ w ∈ keys n, w ≤ v' → get t' w = S p w := by
        intro v' hv' w hw hw'
        rw [he,get_insert,if_neg (by have := hvr v' hv'; omega)]
        exact ht v' (List.mem_cons_of_mem _ hv') w hw hw'
      rw [ih (List.pairwise_cons.mp hl).2 (fun w hw => hsub w (List.mem_cons_of_mem _ hw))
        t' hinit]
      by_cases hk : k∈vs
      · simp [hk, List.mem_cons_of_mem v hk]
      · rw [if_neg hk,he,get_insert]
        by_cases hvk : v=k
        · subst k
          rw [if_pos rfl, if_pos (by simp)]
          rw [ht v (by simp) v (hsub v (by simp)) le_rfl,
              ht v (by simp) (v/p) (mem_keys_div (hsub v (by simp)) hp.pos) (Nat.div_le_self ..)]
          have hh : p-1∈keys n := mem_keys.mpr (Or.inl (by omega))
          have hp' : p≤p*p := by simpa using Nat.mul_le_mul_left p hp.one_lt.le
          have hh' : p-1≤v := by omega
          rw [ht v (by simp) (p-1) hh hh', S_update hp h]
        · simp [hvk,Ne.symm hvk,hk]
    · rw [if_neg h]
      by_cases hk : k∈v::vs
      · rw [if_pos hk]
        have hkv : k ≤ v := (List.mem_cons.mp hk).elim (fun h => h.le) (fun h => (hvr k h).le)
        rw [S_same (Or.inr (by omega))]
        exact ht v (by simp) k (hsub k hk) hkv
      · simp [hk]

theorem loop_correct {n p fuel : ℕ} (hp : 2≤p) (hf : p+fuel≤n.sqrt+1)
    (t : Table) (ht : ∀ k ∈ keys n, get t k = S p k)
    (k : ℕ) (hk : k ∈ keys n) :
    get (loop (keys n) p fuel t) k = S (p+fuel) k := by
  induction fuel generalizing p t with
  | zero => simpa [loop] using ht k hk
  | succ f ih =>
    have h₁ : p ≤ n.sqrt := by omega
    have hb : p-1∈keys n := mem_keys.mpr (Or.inl (by omega))
    have hc : p∈keys n := mem_keys.mpr (Or.inl h₁)
    have hstep : ∀ w ∈ keys n,
        get (if get t (p-1) < get t p then pass p (keys n) t else t) w
         = S (p+1) w := by
      intro w hw
      rw [ht _ hb, ht _ hc]
      by_cases h : p.Prime
      · rw [if_pos ((prime_test hp).mpr h),
           pass_correct h h₁ (keys n) (keys_descending _) (fun _ h => h)
             t (fun _ _ w hw _ => ht w hw) w, if_pos hw]
      · rw [if_neg (fun hc => h ((prime_test hp).mp hc)), S_same (Or.inl h)]
        exact ht w hw
    rw [loop,ih (p:=p+1) (by omega) (by omega) _ hstep,
      show p+1+f = p+(f+1) by omega]

theorem count_correct (n : ℕ) : count n = n.primeCounting := by
  unfold count
  by_cases h : n<2
  · simpa [h] using (Nat.primeCounting_eq_zero_iff.mpr (show n≤1 by omega)).symm
  · rw [if_neg h]
    have hs : 1 ≤ n.sqrt := Nat.le_sqrt.mpr (by omega)
    have he : 2+(n.sqrt-1)=n.sqrt+1 := by omega
    have init : ∀ k∈ keys n, get (initialise (keys n) ∅) k = S 2 k := by
      intro k hk
      rw [initialise_correct,if_pos hk,S_initial]
    rw [loop_correct (by omega) (by omega : 2+(n.sqrt-1)≤n.sqrt+1)
      _ init _ (self_mem_keys _),he,S_terminal]

#print axioms count_correct
end LocalPrimeSieve
