/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2SumBridge.Instances
namespace FKS2Table4
open SumStability

/-- Integer-grid nearestness; no enumeration of binary64 competitors. -/
theorem grid_nearest (d : ℚ) (hd : 0<d) (m j : ℤ) (x : ℚ)
    (h : |(m : ℚ) * d - x| ≤ d / 2) :
    |(m : ℚ) * d - x| ≤ |(j : ℚ) * d - x| := by
  have hu : 0<d := hd
  have hh := abs_le.mp h
  rcases lt_trichotomy j m with hj | rfl | hj
  · have hi : (j : ℚ) + 1 ≤ m := by exact_mod_cast (show j + 1 ≤ m by omega)
    have hd : (j : ℚ) * d - x ≤ 0 := by nlinarith
    rw [abs_of_nonpos hd]
    exact (abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
  · rfl
  · have hi : (m : ℚ) + 1 ≤ j := by exact_mod_cast (show m + 1 ≤ j by omega)
    have hd : 0 ≤ (j : ℚ) * d - x := by nlinarith
    rw [abs_of_nonneg hd]
    exact (abs_le.mpr ⟨by nlinarith, by nlinarith⟩)

/-- A nonidentical grid competitor can tie only at half an ulp. -/
theorem grid_tie (d : ℚ) (hd : 0<d) (m j : ℤ) (x : ℚ) (hne : j ≠ m)
    (h : |(m : ℚ) * d - x| ≤ d / 2)
    (he : |(j : ℚ) * d - x| = |(m : ℚ) * d - x|) :
    |(m : ℚ) * d - x| = d / 2 := by
  have hu : 0<d := hd
  have hdist : d ≤ |((m - j : ℤ) : ℚ) * d| := by
    have hij : (1 : ℤ) ≤ |m - j| := by
      have hp : 0 < |m - j| := abs_pos.mpr (by omega)
      omega
    have hijq : (1 : ℚ) ≤ |(m : ℚ) - j| := by exact_mod_cast hij
    rw [Int.cast_sub, abs_mul, abs_of_pos hu]
    nlinarith
  have ht := abs_add_le ((m : ℚ) * d - x) (x - (j : ℚ) * d)
  rw [abs_sub_comm x ((j : ℚ) * d), he] at ht
  have hid : ((m : ℚ) * d - x) + (x - (j : ℚ) * d) =
      ((m - j : ℤ) : ℚ) * d := by push_cast; ring
  rw [hid] at ht
  linarith


/-- A competitor above2^k has a dyadic representation on this binade's grid. -/
theorem binary64_grid (k : ℤ) {z : ℚ} (hz : Binary64 z) (hzlo : (2:ℚ)^k ≤ z) :
    ∃ j : ℤ, z = (j:ℚ)*(2:ℚ)^(k-52) := by
  obtain ⟨m,e,hm,helo,hehi,hval⟩ := hz
  have hp : (0:ℚ)<(2:ℚ)^e := zpow_pos (by norm_num) _
  have hmpos : (0:ℚ)<m := by nlinarith [zpow_pos (by norm_num : (0:ℚ)<2) k]
  have hmhi : (m:ℚ)<2^53 := by exact_mod_cast (lt_of_le_of_lt (le_abs_self m) hm)
  have he : k-52 ≤ e := by
    by_contra h
    have hle : e ≤ k-53 := by omega
    have hx : z < (2:ℚ)^k := by
      calc
        z = (m:ℚ)*(2:ℚ)^e := hval
        _ ≤ (m:ℚ)*(2:ℚ)^(k-53) :=
          mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hle) hmpos.le
        _ < (2:ℚ)^53*(2:ℚ)^(k-53) := mul_lt_mul_of_pos_right hmhi (by positivity)
        _ = _ := by rw [← zpow_natCast,← zpow_add₀ (by norm_num)];congr 1;omega
    linarith
  refine ⟨m*2^(e-(k-52)).toNat,?_⟩
  have hnat : ((e-(k-52)).toNat:ℤ)=e-(k-52) := Int.toNat_of_nonneg (by omega)
  have hpow : (2:ℚ)^(e-(k-52)).toNat*(2:ℚ)^(k-52)=(2:ℚ)^e := by
    rw [← zpow_natCast,hnat,← zpow_add₀ (by norm_num)];congr 1;ring
  rw [hval]
  push_cast
  rw [mul_assoc,hpow]

theorem scoped_RN64 (k m : ℤ) (x : ℚ) (hk : -100 ≤ k ∧ k ≤ 100)
    (hm : 2^52 ≤ m ∧ m<2^53)
    (hx : (2:ℚ)^k+(2:ℚ)^(k-52)/2 ≤ x ∧ x ≤ (2:ℚ)^(k+1)-(2:ℚ)^(k-52)/2)
    (herr : |(m:ℚ)*(2:ℚ)^(k-52)-x| ≤ (2:ℚ)^(k-52)/2)
    (htie : |(m:ℚ)*(2:ℚ)^(k-52)-x| = (2:ℚ)^(k-52)/2 → Even m) :
    RN64 x ((m:ℚ)*(2:ℚ)^(k-52)) := by
  let d : ℚ := (2:ℚ)^(k-52)
  have hd : 0<d := by dsimp [d];positivity
  have hy : Binary64 ((m:ℚ)*d) :=
    ⟨m,k-52,by rw [abs_of_nonneg (by omega)];omega,by omega,by omega,rfl⟩
  have hnearest (z : ℚ) (hz : Binary64 z) : |(m:ℚ)*d-x| ≤ |z-x| := by
    by_cases hlo : z<(2:ℚ)^k
    · rw [abs_of_neg (show z-x<0 by linarith [hx.1])]
      linarith [hx.1]
    · obtain ⟨j,rfl⟩ := binary64_grid k hz (le_of_not_gt hlo)
      exact grid_nearest d hd m j x herr
  refine ⟨hy,hnearest,?_⟩
  rintro ⟨z,hz,hne,he⟩
  have hzlo : (2:ℚ)^k ≤ z := by
    by_contra h
    have hn : z-x<0 := by linarith [hx.1]
    rw [abs_of_neg hn] at he
    linarith [hx.1]
  obtain ⟨j,hj⟩ := binary64_grid k hz hzlo
  have hjne : j≠m := by intro h;subst j;exact hne hj
  have ht := grid_tie d hd m j x hjne herr (by simpa [hj] using he)
  right;right
  refine ⟨m,k-52,?_,?_,by omega,by omega,rfl,htie ht⟩
  · rw [abs_of_nonneg (by omega)];exact hm.1
  · rw [abs_of_nonneg (by omega)];exact hm.2

def additionCheck (x y : ℚ) : Bool :=
  if x==y then FKS2SumBridge.reprCheck y else
    let k := FKS2SumBridge.exponentOf y+52
    let m := FKS2SumBridge.mantissaOf y
    decide (-100 ≤ k ∧ k ≤ 100 ∧ 2^52 ≤ m ∧ m<2^53 ∧
      y=(m:ℚ)*(2:ℚ)^(k-52) ∧
      ((2:ℚ)^k+(2:ℚ)^(k-52)/2 ≤ x ∧ x ≤ (2:ℚ)^(k+1)-(2:ℚ)^(k-52)/2) ∧
      |y-x| ≤ (2:ℚ)^(k-52)/2 ∧ (|y-x|=(2:ℚ)^(k-52)/2 → Even m))

theorem additionCheck_sound {x y : ℚ} (h : additionCheck x y = true) : RN64 x y := by
  unfold additionCheck at h
  split at h
  · rename_i he
    have hxy : x=y := by simpa using he
    subst x
    exact rn_self (FKS2SumBridge.reprCheck_sound h)
  · have hc := of_decide_eq_true h
    rcases hc with ⟨hkl,hku,hml,hmu,hy,hx,herr,htie⟩
    have hh := scoped_RN64 _ _ _ ⟨hkl,hku⟩ ⟨hml,hmu⟩ hx
      (by simpa only [← hy] using herr) (by simpa only [← hy] using htie)
    simpa only [← hy] using hh
end FKS2Table4
