import SumStability.Rounding
import FKS2Scalar.Model

namespace FKS2SumBridge
open SumStability

def unit : ℚ := 1 / 2 ^ 52

/-- Every finite binary64 value at least one lies on the 2^-52 grid. -/
theorem binary64_grid {z : ℚ} (hz : Binary64 z) (hzlo : 1 ≤ z) :
    ∃ j : ℤ, z = (j : ℚ) * unit := by
  obtain ⟨m, e, hm, helo, hehi, hval⟩ := hz
  have hp : (0 : ℚ) < (2 : ℚ) ^ e := zpow_pos (by norm_num) _
  have hmpos : (0 : ℚ) < m := by nlinarith
  have hmn : 0 ≤ m := by exact_mod_cast hmpos.le
  have hmhi : (m : ℚ) < 2 ^ 53 := by exact_mod_cast (lt_of_le_of_lt (le_abs_self m) hm)
  have he : -52 ≤ e := by
    by_contra h
    have hle : e ≤ -53 := by omega
    have hpow : (2 : ℚ) ^ e ≤ (2 : ℚ) ^ (-53 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) hle
    have hx : z < 1 := by
      calc
        z = (m : ℚ) * (2 : ℚ) ^ e := hval
        _ ≤ (m : ℚ) * (2 : ℚ) ^ (-53 : ℤ) := mul_le_mul_of_nonneg_left hpow hmpos.le
        _ < (2 : ℚ) ^ 53 * (2 : ℚ) ^ (-53 : ℤ) :=
          mul_lt_mul_of_pos_right hmhi (by positivity)
        _ = 1 := by norm_num
    linarith
  refine ⟨m * 2 ^ (e + 52).toNat, ?_⟩
  have hnat : ((e + 52).toNat : ℤ) = e + 52 := Int.toNat_of_nonneg (by omega)
  have hpow : (2 : ℚ) ^ (e + 52).toNat * (2 : ℚ) ^ (-52 : ℤ) = (2 : ℚ) ^ e := by
    rw [← zpow_natCast, hnat, ← zpow_add₀ (by norm_num)]
    congr 1
    omega
  rw [hval]
  push_cast
  have hu : unit = (2 : ℚ) ^ (-52 : ℤ) := by norm_num [unit]
  rw [hu, mul_assoc, hpow]

/-- Integer-grid nearestness; no enumeration of binary64 competitors. -/
theorem grid_nearest (m j : ℤ) (x : ℚ)
    (h : |(m : ℚ) * unit - x| ≤ unit / 2) :
    |(m : ℚ) * unit - x| ≤ |(j : ℚ) * unit - x| := by
  have hu : 0 < unit := by norm_num [unit]
  have hh := abs_le.mp h
  rcases lt_trichotomy j m with hj | rfl | hj
  · have hi : (j : ℚ) + 1 ≤ m := by exact_mod_cast (show j + 1 ≤ m by omega)
    have hd : (j : ℚ) * unit - x ≤ 0 := by nlinarith
    rw [abs_of_nonpos hd]
    exact (abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
  · rfl
  · have hi : (m : ℚ) + 1 ≤ j := by exact_mod_cast (show m + 1 ≤ j by omega)
    have hd : 0 ≤ (j : ℚ) * unit - x := by nlinarith
    rw [abs_of_nonneg hd]
    exact (abs_le.mpr ⟨by nlinarith, by nlinarith⟩)

/-- A nonidentical grid competitor can tie only at half an ulp. -/
theorem grid_tie (m j : ℤ) (x : ℚ) (hne : j ≠ m)
    (h : |(m : ℚ) * unit - x| ≤ unit / 2)
    (he : |(j : ℚ) * unit - x| = |(m : ℚ) * unit - x|) :
    |(m : ℚ) * unit - x| = unit / 2 := by
  have hu : 0 < unit := by norm_num [unit]
  have hdist : unit ≤ |((m - j : ℤ) : ℚ) * unit| := by
    have hij : (1 : ℤ) ≤ |m - j| := by
      have hp : 0 < |m - j| := abs_pos.mpr (by omega)
      omega
    have hijq : (1 : ℚ) ≤ |(m : ℚ) - j| := by exact_mod_cast hij
    rw [Int.cast_sub, abs_mul, abs_of_pos hu]
    nlinarith
  have ht := abs_add_le ((m : ℚ) * unit - x) (x - (j : ℚ) * unit)
  rw [abs_sub_comm x ((j : ℚ) * unit), he] at ht
  have hid : ((m : ℚ) * unit - x) + (x - (j : ℚ) * unit) =
      ((m - j : ℤ) : ℚ) * unit := by push_cast; ring
  rw [hid] at ht
  linarith

/-- Reusable certificate soundness for the actual FKS2 accumulator binade.
Finite checks establish these rational premises for source-derived addition events. -/
theorem scoped_RN64 (x : ℚ) (m : ℤ)
    (hm : 2 ^ 52 ≤ m ∧ m < 2 ^ 53)
    (hx : 1 + unit / 2 ≤ x ∧ x ≤ 2 - unit / 2)
    (herr : |(m : ℚ) * unit - x| ≤ unit / 2)
    (htie : |(m : ℚ) * unit - x| = unit / 2 → Even m) :
    RN64 x ((m : ℚ) * unit) := by
  have hu : 0 < unit := by norm_num [unit]
  have hy : Binary64 ((m : ℚ) * unit) := by
    refine ⟨m, -52, ?_, by norm_num, by norm_num, ?_⟩
    · rw [abs_of_nonneg (by omega)]
      exact hm.2
    · norm_num [unit]
  have hnearest (z : ℚ) (hz : Binary64 z) :
      |(m : ℚ) * unit - x| ≤ |z - x| := by
    by_cases hlo : z < 1
    · have : z - x < 0 := by linarith [hx.1]
      rw [abs_of_neg this]
      linarith [hx.1]
    · obtain ⟨j, rfl⟩ := binary64_grid hz (le_of_not_gt hlo)
      exact grid_nearest m j x herr
  refine ⟨hy, hnearest, ?_⟩
  rintro ⟨z, hz, hne, he⟩
  have hzlo : 1 ≤ z := by
    by_contra hzlo
    have hzlt : z < 1 := lt_of_not_ge hzlo
    have hneg : z - x < 0 := by linarith [hx.1]
    rw [abs_of_neg hneg] at he
    linarith [hx.1]
  obtain ⟨j, hj⟩ := binary64_grid hz hzlo
  have hjne : j ≠ m := by intro h; subst j; exact hne hj
  have ht := grid_tie m j x hjne herr (by simpa [hj] using he)
  right; right
  refine ⟨m, -52, ?_, ?_, by norm_num, by norm_num, ?_, htie ht⟩
  · rw [abs_of_nonneg (by omega)]; exact hm.1
  · rw [abs_of_nonneg (by omega)]; exact hm.2
  · norm_num [unit]

end FKS2SumBridge
