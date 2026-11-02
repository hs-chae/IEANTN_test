import SumStability.Rounding

namespace SumStability

def gamma (k : ℕ) : ℚ := (k : ℚ) * u / (1 - (k : ℚ) * u)

def ValidInputs (xs : List ℚ) : Prop :=
  ∀ x ∈ xs, Binary64 x ∧ low ≤ x ∧ x ≤ 1

/-- The ordered list of loads, accumulated from zero with one RN64 addition per load. -/
inductive Accum : List ℚ → ℚ → Prop
  | zero : Accum [] 0
  | step {xs : List ℚ} {s x r : ℚ} :
      Accum xs s → RN64 (s + x) r → Accum (xs ++ [x]) r

theorem gamma_den {k : ℕ} (hk : k ≤ 64) : 0 < 1 - (k : ℚ) * u := by
  have hc : (k : ℚ) ≤ 64 := by exact_mod_cast hk
  norm_num [u]
  linarith

theorem gamma_nonneg {k : ℕ} (hk : k ≤ 64) : 0 ≤ gamma k := by
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num [u]))
    (gamma_den hk).le

theorem gamma_step {k : ℕ} (hk : k + 1 ≤ 64) :
    (1 + u) * gamma k + u ≤ gamma (k + 1) := by
  have h₀ := gamma_den (show k ≤ 64 by omega)
  have h₁ := gamma_den hk
  have he : (1 + u) * gamma k + u = ((k : ℚ) + 1) * u / (1 - (k : ℚ) * u) := by
    unfold gamma
    apply (eq_div_iff h₀.ne').mpr
    calc
      ((1 + u) * ((k : ℚ) * u / (1 - (k : ℚ) * u)) + u) *
          (1 - (k : ℚ) * u) =
          (1 + u) * (((k : ℚ) * u / (1 - (k : ℚ) * u)) *
            (1 - (k : ℚ) * u)) + u * (1 - (k : ℚ) * u) := by ring
      _ = ((k : ℚ) + 1) * u := by rw [div_mul_cancel₀ _ h₀.ne']; ring
  rw [he]
  unfold gamma
  push_cast at h₁ ⊢
  exact div_le_div_of_nonneg_left (by dsimp [u]; positivity) h₁ (by
    have : 0 ≤ u := by norm_num [u]
    linarith)

theorem gamma_ge_u {k : ℕ} (hk : k ≤ 64) (hk₁ : 1 ≤ k) : u ≤ gamma k := by
  have hd := gamma_den hk
  have hcast : (1 : ℚ) ≤ k := by exact_mod_cast hk₁
  rw [gamma, le_div_iff₀ hd]
  have hu : 0 ≤ u := by norm_num [u]
  have hku := mul_le_mul_of_nonneg_right hcast hu
  have huu := mul_nonneg hu (mul_nonneg (Nat.cast_nonneg k) hu)
  nlinarith

/-- Safety and forward error at every nonempty prefix. -/
def Invariant (xs : List ℚ) (s : ℚ) : Prop :=
  (xs = [] → s = 0) ∧
  (xs ≠ [] → low ≤ s ∧ s ≤ 2 * (xs.length : ℚ) ∧ Binary64 s ∧
    |s - xs.sum| ≤ gamma (xs.length - 1) * xs.sum)

theorem accum_invariant {xs : List ℚ} {s : ℚ} (hexec : Accum xs s)
    (hdomain : ValidInputs xs) (hlen : xs.length ≤ 64) : Invariant xs s := by
  induction hexec with
  | zero => simp [Invariant]
  | @step ys s x r hexec hadd ih =>
    have hys : ValidInputs ys := by
      intro z hz
      exact hdomain z (List.mem_append_left _ hz)
    have hx := hdomain x (by simp)
    have hyn : ys.length ≤ 63 := by simp only [List.length_append, List.length_singleton] at hlen; omega
    have ih := ih hys (by omega)
    refine ⟨by simp, ?_⟩
    intro _
    by_cases hempty : ys = []
    · subst ys
      have hs := ih.1 rfl
      subst s
      have hr : r = x := rn_exact hx.1 (by simpa using hadd)
      subst r
      simpa [gamma, u] using And.intro hx.2.1 (And.intro (by linarith [hx.2.2])
        (And.intro hx.1 (show (0 : ℚ) ≤ 0 by rfl)))
    · obtain ⟨hslo, hshi, hsfinite, herr⟩ := ih.2 hempty
      have hnpos : 1 ≤ ys.length := List.length_pos_iff.mpr hempty
      have hnq : (ys.length : ℚ) ≤ 63 := by exact_mod_cast hyn
      have htlo : low ≤ s + x := by linarith [hx.2.1, (show (0 : ℚ) < low by norm_num [low])]
      have hthi : s + x ≤ 128 := by linarith [hx.2.2]
      have hround := rn_relative htlo hthi hadd
      have hu : 0 < u := by norm_num [u]
      have hsmall : u ≤ 1 / 128 := by norm_num [u]
      have hrange := abs_le.mp hround
      have hrlo : low ≤ r := by
        have ht : 2 * low ≤ s + x := by linarith [hx.2.1]
        have hu' : u ≤ 1 / 2 := by linarith
        have htpos : 0 ≤ s + x := le_trans (by norm_num [low]) htlo
        nlinarith
      have hrhi : r ≤ 2 * ((ys ++ [x]).length : ℚ) := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        have htpos : 0 ≤ s + x := le_trans (by norm_num [low]) htlo
        have : u * (s + x) ≤ 1 := by
          have := mul_le_mul_of_nonneg_right hsmall htpos
          nlinarith
        linarith [hx.2.2]
      refine ⟨hrlo, hrhi, hadd.1, ?_⟩
      have hS : 0 ≤ ys.sum := List.sum_nonneg (fun z hz => by
        linarith [(hys z hz).2.1, (show (0 : ℚ) < low by norm_num [low])])
      have hxpos : 0 ≤ x := by linarith [hx.2.1, (show (0 : ℚ) < low by norm_num [low])]
      have hg := gamma_nonneg (show ys.length - 1 ≤ 64 by omega)
      have hstep := gamma_step (show (ys.length - 1) + 1 ≤ 64 by omega)
      have heq : ys.length - 1 + 1 = ys.length := by omega
      rw [heq] at hstep
      have hgu := gamma_ge_u (show ys.length ≤ 64 by omega) hnpos
      have herrhi := (abs_le.mp herr).2
      have htri : |r - (ys.sum + x)| ≤ |r - (s + x)| + |s - ys.sum| := by
        have he : r - (ys.sum + x) = (r - (s + x)) + (s - ys.sum) := by ring
        rw [he]
        exact abs_add_le _ _
      have hfirst : |r - (s + x)| + |s - ys.sum| ≤
          ((1 + u) * gamma (ys.length - 1) + u) * ys.sum + u * x := by
        have hm := mul_le_mul_of_nonneg_left herrhi hu.le
        linarith
      have hfinal : ((1 + u) * gamma (ys.length - 1) + u) * ys.sum + u * x ≤
          gamma ys.length * (ys.sum + x) := by
        have ha := mul_le_mul_of_nonneg_right hstep hS
        have hb := mul_le_mul_of_nonneg_right hgu hxpos
        nlinarith
      simpa using htri.trans (hfirst.trans hfinal)

theorem sumAbs_eq_sum {xs : List ℚ} (hd : ValidInputs xs) :
    (xs.map abs).sum = xs.sum := by
  apply congrArg List.sum
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [abs_of_nonneg (by linarith [(hd x (by simp)).2.1,
      (show (0 : ℚ) < low by norm_num [low])]), ih]
    intro z hz
    exact hd z (by simp [hz])

end SumStability
