/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Correction.Consumer

namespace FKS2Correction
open FKS2Scalar

def helperTolerance (e : HelperEvent) : ℚ :=
  if e.arg < -10 then 1/10^20 else if 10 < e.arg then 1/10^6 else 1/10^11

def rootCheck300 (x p : ℚ) : Bool := decide (
  0 ≤ p-1/10^9 ∧ (p-1/10^9)^2 ≤ x ∧ x ≤ (p+1/10^9)^2)

def audit300 (e : HelperEvent) : Bool :=
  if e.name == "exp_small" then
    expCheck e.arg (e.out-helperTolerance e) (e.out+helperTolerance e)
  else if e.name == "sqrt_fixed" then rootCheck300 e.arg e.out else false

def powerProducts : Nat → ℚ → ℚ → Option ℚ
  | 0, acc, _ => some acc
  | n+1, acc, seed => do
      let out ← round64 (acc*seed)
      powerProducts n out seed

def seed15 : ℚ := (get baselineFrame.env "e15").getD 0
def seed20 : ℚ := (get baselineFrame.env "e20").getD 0
def power150 : ℚ := (get baselineFrame.env "e150").getD 0
def power200 : ℚ := (get baselineFrame.env "e200").getD 0

theorem baseline_helpers_checked : ∀ e ∈ baselineEvents, audit300 e = true := by
  native_decide

theorem power_product_checks :
    powerProducts 9 seed15 seed15 = some power150 ∧
    powerProducts 9 seed20 seed20 = some power200 ∧
    |power150-seed15^10| ≤ (1:ℚ)/10^79 ∧
    |power200-seed20^10| ≤ (1:ℚ)/10^100 ∧
    seed15 = ((baselineEvents[85]?).getD (⟨"",0,0⟩ : HelperEvent)).out ∧
    seed20 = ((baselineEvents[86]?).getD (⟨"",0,0⟩ : HelperEvent)).out := by
  native_decide

theorem rootCheck300_sound {x p : ℚ} (h : rootCheck300 x p = true) :
    |(p:ℝ)-Real.sqrt (x:ℝ)| ≤ (1:ℝ)/10^9 := by
  have hr := of_decide_eq_true h
  change 0 ≤ p-1/10^9 ∧ (p-1/10^9)^2 ≤ x ∧ x ≤ (p+1/10^9)^2 at hr
  have hp : (0:ℝ) ≤ (p:ℝ)-1/10^9 := by
    simpa using (Rat.cast_le (K := ℝ)).2 hr.1
  have hl : ((p:ℝ)-1/10^9)^2 ≤ (x:ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).2 hr.2.1
  have hu : (x:ℝ) ≤ ((p:ℝ)+1/10^9)^2 := by
    simpa using (Rat.cast_le (K := ℝ)).2 hr.2.2
  have hrl := Real.le_sqrt_of_sq_le hl
  have hru := Real.sqrt_le_iff.mpr ⟨(by linarith : (0:ℝ) ≤ (p:ℝ)+1/10^9),hu⟩
  rw [abs_le]
  constructor <;> linarith

theorem reachable_helper_error300 (e : HelperEvent) (he : e ∈ baselineEvents) :
    (e.name = "exp_small" ∧
      |(e.out:ℝ)-Real.exp (e.arg:ℝ)| ≤ (helperTolerance e:ℝ)) ∨
    (e.name = "sqrt_fixed" ∧
      |(e.out:ℝ)-Real.sqrt (e.arg:ℝ)| ≤ (1:ℝ)/10^9) := by
  have h := baseline_helpers_checked e he
  unfold audit300 at h
  by_cases hn : e.name = "exp_small"
  · simp only [hn, beq_self_eq_true, ↓reduceIte] at h
    have hx := expCheck_sound h
    push_cast at hx
    left
    refine ⟨hn, ?_⟩
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  · by_cases hs : e.name = "sqrt_fixed"
    · simp [hn,hs] at h
      exact Or.inr ⟨hs,rootCheck300_sound h⟩
    · simp [hn,hs] at h

end FKS2Correction
