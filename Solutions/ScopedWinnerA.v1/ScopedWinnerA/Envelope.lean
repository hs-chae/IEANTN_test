/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedWinnerA.Comparison
namespace ScopedWinnerA.Comparison
open Real IEANTN
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All frozen output identities; duplicate allowances are deliberately retained. -/
noncomputable def incumbent (x : ℝ) : Fin 37 → ℝ :=
  ![admissibleBound 9.2211 (3/2) 0.84768363 1 x,
    admissibleBound 0.826 (1/4) 1 5.5666305 x,
    (0.4298:ℝ),
    min (admissibleBound 9.2211 (3/2) 0.84768363 1 x) (admissibleBound (3/100000000) 2 2 1 x),
    min (admissibleBound 0.826 (1/4) 1 5.5666305 x) (admissibleBound (3/100000000) 2 2 1 x),
    admissibleBound (16/100000000) 2 2 1 x,
    (1.6855e-12:ℝ),
    ((5:ℝ)/10^16),
    (1.69e-12:ℝ),
    ((5:ℝ)/10^16),
    min (1.69e-12:ℝ) ((5:ℝ)/10^16),
    admissibleBound 9.2211 (3/2) 0.84768363 1 x,
    admissibleBound 0.826 (1/4) 1 5.5666305 x,
    ((5:ℝ)/10^16),
    (1.69e-12:ℝ),
    ((5:ℝ)/10^16),
    (0.01323:ℝ)*scale x,
    admissibleBound (3/100000000) 2 2 1 x,
    ((1001/1000:ℝ)*(9474448/1000000000)+1/100000000)*scale x,
    (0.009898)*scale x,
    (0.009830)*scale x,
    (0.009898)*scale x,
    (0.009830)*scale x,
    (oldExact)*scale x,
    (0.009952)*scale x,
    (473723/50000000)*scale x,
    (0.009952)*scale x,
    (0.013170)*scale x,
    (2371/250000)*scale x,
    (0.009952)*scale x,
    (0.009898)*scale x,
    (0.009830)*scale x,
    (473723/50000000)*scale x,
    (2371/250000)*scale x,
    (671/500000)*(log x)^2*x^(((9/10):ℝ)-1),
    (21/1000)*(log x)^2*x^(((9/10):ℝ)-1),
    (957/500000)*(log x)^2*x^(((7/8):ℝ)-1)]
noncomputable def oldEnvelope (x : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (incumbent x)

theorem incumbent_lower {x : ℝ} (hx : domain x) :
    ∀ i : Fin 37, oldExact * scale x ≤ incumbent x i := by
  have hold : oldExact*scale x≤(473723/50000000:ℝ)*scale x := power_floor hx le_rfl
  have h22 := standard_curve hx (by norm_num : (1/100:ℝ)≤9.2211)
    (by norm_num : (0:ℝ)≤3/2) (by norm_num : (0:ℝ)≤0.84768363)
    (by norm_num : (0.84768363:ℝ)≤2) (by norm_num : (1:ℝ)≤1) (by norm_num : (1:ℝ)≤6)
  have h23 := standard_curve hx (by norm_num : (1/100:ℝ)≤0.826)
    (by norm_num : (0:ℝ)≤1/4) (by norm_num : (0:ℝ)≤1)
    (by norm_num : (1:ℝ)≤2) (by norm_num : (1:ℝ)≤5.5666305) (by norm_num : (5.5666305:ℝ)≤6)
  have h3 := classical3 hx
  have htiny := numeric_tiny hx
  have hrounded : admissibleBound (3/100000000) 2 2 1 x ≤
      admissibleBound (16/100000000) 2 2 1 x := by
    unfold admissibleBound
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    apply mul_le_mul_of_nonneg_right (by norm_num) (rpow_nonneg (by have h:=(logs hx).1;linarith) _)
  intro i
  fin_cases i
  · change oldExact * scale x ≤ (admissibleBound 9.2211 (3/2) 0.84768363 1 x)
    exact hold.trans h22.le
  · change oldExact * scale x ≤ (admissibleBound 0.826 (1/4) 1 5.5666305 x)
    exact hold.trans h23.le
  · change oldExact * scale x ≤ ((0.4298:ℝ))
    exact hold.trans (htiny.trans_le (by norm_num)).le
  · change oldExact * scale x ≤ (min (admissibleBound 9.2211 (3/2) 0.84768363 1 x) (admissibleBound (3/100000000) 2 2 1 x))
    exact hold.trans (lt_min h22 h3).le
  · change oldExact * scale x ≤ (min (admissibleBound 0.826 (1/4) 1 5.5666305 x) (admissibleBound (3/100000000) 2 2 1 x))
    exact hold.trans (lt_min h23 h3).le
  · change oldExact * scale x ≤ (admissibleBound (16/100000000) 2 2 1 x)
    exact hold.trans (h3.trans_le hrounded).le
  · change oldExact * scale x ≤ ((1.6855e-12:ℝ))
    exact hold.trans (htiny.trans_le (by norm_num)).le
  · change oldExact * scale x ≤ (((5:ℝ)/10^16))
    exact hold.trans htiny.le
  · change oldExact * scale x ≤ ((1.69e-12:ℝ))
    exact hold.trans (htiny.trans_le (by norm_num)).le
  · change oldExact * scale x ≤ (((5:ℝ)/10^16))
    exact hold.trans htiny.le
  · change oldExact * scale x ≤ (min (1.69e-12:ℝ) ((5:ℝ)/10^16))
    exact hold.trans (lt_min (htiny.trans_le (by norm_num)) htiny).le
  · change oldExact * scale x ≤ (admissibleBound 9.2211 (3/2) 0.84768363 1 x)
    exact hold.trans h22.le
  · change oldExact * scale x ≤ (admissibleBound 0.826 (1/4) 1 5.5666305 x)
    exact hold.trans h23.le
  · change oldExact * scale x ≤ (((5:ℝ)/10^16))
    exact hold.trans htiny.le
  · change oldExact * scale x ≤ ((1.69e-12:ℝ))
    exact hold.trans (htiny.trans_le (by norm_num)).le
  · change oldExact * scale x ≤ (((5:ℝ)/10^16))
    exact hold.trans htiny.le
  · change oldExact * scale x ≤ ((0.01323:ℝ)*scale x)
    exact power_floor hx (by norm_num)
  · change oldExact * scale x ≤ (admissibleBound (3/100000000) 2 2 1 x)
    exact hold.trans h3.le
  · change oldExact * scale x ≤ (((1001/1000:ℝ)*(9474448/1000000000)+1/100000000)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((0.009898)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((0.009830)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((0.009898)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((0.009830)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((oldExact)*scale x)
    exact le_rfl
  · change oldExact * scale x ≤ ((0.009952)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((473723/50000000)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((0.009952)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((0.013170)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((2371/250000)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((0.009952)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((0.009898)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((0.009830)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((473723/50000000)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((2371/250000)*scale x)
    exact power_floor hx (by norm_num [oldExact])
  · change oldExact * scale x ≤ ((671/500000)*(log x)^2*x^(((9/10):ℝ)-1))
    exact hold.trans (log2_power (C:=(671/500000)) (β:=(9/10)) hx (by norm_num) (by norm_num)).le
  · change oldExact * scale x ≤ ((21/1000)*(log x)^2*x^(((9/10):ℝ)-1))
    exact hold.trans (log2_power (C:=(21/1000)) (β:=(9/10)) hx (by norm_num) (by norm_num)).le
  · change oldExact * scale x ≤ ((957/500000)*(log x)^2*x^(((7/8):ℝ)-1))
    exact hold.trans (log2_power (C:=(957/500000)) (β:=(7/8)) hx (by norm_num) (by norm_num)).le

theorem old_envelope_exact {x : ℝ} (hx : domain x) :
    oldEnvelope x=oldExact*scale x := by
  apply le_antisymm
  · exact Finset.inf'_le (incumbent x) (Finset.mem_univ (23:Fin 37))
  · exact Finset.le_inf' Finset.univ_nonempty (incumbent x) (by intro i _;exact incumbent_lower hx i)

/-- Uniform strict comparison against the entire frozen envelope, not an endpoint sample. -/
theorem scoped_strict {x : ℝ} (hx : domain x) :
    newCap*scale x+(298/100000000:ℝ)*scale x < oldEnvelope x := by
  rw [old_envelope_exact hx]
  exact strict_increment hx
#print axioms incumbent_lower
#print axioms old_envelope_exact
#print axioms scoped_strict
end ScopedWinnerA.Comparison
