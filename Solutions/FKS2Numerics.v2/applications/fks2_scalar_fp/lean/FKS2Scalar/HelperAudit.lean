import FKS2Scalar.SourceSafety

namespace FKS2Scalar

def helperEvents : List HelperEvent :=
  ((executeObserved round64 selectedAST).map Prod.snd).getD []

def helperIdeal (event : HelperEvent) : Option Rat := do
  let f ← selectedAST.find? (fun f => f.name == event.name)
  let param ← f.param
  let (final, _) ← (evalBlock some selectedAST 1024 ⟨[(param, event.arg)], none⟩ f.body).run []
  final.result

def sqrtCheck (x p : Rat) : Bool := decide (
  0 ≤ p - 1 / 10 ^ 15 ∧ (p - 1 / 10 ^ 15) ^ 2 ≤ x ∧ x ≤ (p + 1 / 10 ^ 15) ^ 2)

def auditHelper (event : HelperEvent) : Bool :=
  let p := (helperIdeal event).getD 0
  (helperIdeal event == some p) &&
  if event.name == "exp_small" then
    decide (p = expPoly event.arg ^ 32 ∧ |event.out - p| ≤ 1 / 10 ^ 11) &&
    expCheck event.arg (p - 1 / 10 ^ 11) (p + 1 / 10 ^ 11)
  else if event.name == "sqrt_fixed" then
    decide (|event.out - p| ≤ 1 / 10 ^ 14) && sqrtCheck event.arg p
  else false

theorem observed_execution : executeObserved round64 selectedAST = some (q, helperEvents) := by
  native_decide

theorem all_helper_checks : ∀ e ∈ helperEvents, auditHelper e = true := by
  native_decide

theorem helper_counts : helperEvents.length = 87 ∧
    (helperEvents.filter (fun e => e.name == "exp_small")).length = 86 ∧
    (helperEvents.filter (fun e => e.name == "sqrt_fixed")).length = 1 := by
  native_decide

theorem sqrtCheck_sound {x p : Rat} (h : sqrtCheck x p = true) :
    |(p : ℝ) - Real.sqrt (x : ℝ)| ≤ (1 : ℝ) / 10 ^ 15 := by
  have hr := of_decide_eq_true h
  change 0 ≤ p - 1 / 10 ^ 15 ∧ (p - 1 / 10 ^ 15) ^ 2 ≤ x ∧
    x ≤ (p + 1 / 10 ^ 15) ^ 2 at hr
  have hp : (0 : ℝ) ≤ (p : ℝ) - 1 / 10 ^ 15 := by
    simpa using (Rat.cast_le (K := ℝ)).2 hr.1
  have hl : ((p : ℝ) - 1 / 10 ^ 15) ^ 2 ≤ (x : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).2 hr.2.1
  have hu : (x : ℝ) ≤ ((p : ℝ) + 1 / 10 ^ 15) ^ 2 := by
    simpa using (Rat.cast_le (K := ℝ)).2 hr.2.2
  have hrl := Real.le_sqrt_of_sq_le hl
  have hru := Real.sqrt_le_iff.mpr ⟨(by linarith : (0 : ℝ) ≤ (p : ℝ) + 1 / 10 ^ 15), hu⟩
  rw [abs_le]
  constructor <;> linarith

/-- Per-helper analytical and arithmetic errors for every call constructed by source execution.
The final-output budget separately uses the exact whole-source rounding comparison. -/
theorem reachable_helper_error (e : HelperEvent) (he : e ∈ helperEvents) :
    (e.name = "exp_small" ∧
      |(e.out : ℝ) - Real.exp (e.arg : ℝ)| ≤ (2 : ℝ) / 10 ^ 11) ∨
    (e.name = "sqrt_fixed" ∧
      |(e.out : ℝ) - Real.sqrt (e.arg : ℝ)| ≤ (11 : ℝ) / 10 ^ 15) := by
  have h := all_helper_checks e he
  simp only [auditHelper, Bool.and_eq_true] at h
  by_cases hn : e.name = "exp_small"
  · simp only [hn, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
    have hexp := expCheck_sound h.2.2
    have hround : |(e.out : ℝ) - ((helperIdeal e).getD 0 : ℝ)| ≤ (1 : ℝ) / 10 ^ 11 := by
      simpa using (Rat.cast_le (K := ℝ)).2 h.2.1.2
    push_cast at hexp
    left
    refine ⟨hn, ?_⟩
    rw [abs_le] at hround ⊢
    constructor <;> linarith [hexp.1, hexp.2]
  · by_cases hs : e.name = "sqrt_fixed"
    · simp [hs] at h
      have hroot := sqrtCheck_sound h.2.2
      have hround : |(e.out : ℝ) - ((helperIdeal e).getD 0 : ℝ)| ≤ (1 : ℝ) / 10 ^ 14 := by
        simpa using (Rat.cast_le (K := ℝ)).2 h.2.1
      right
      refine ⟨hs, ?_⟩
      rw [abs_le] at hround hroot ⊢
      constructor <;> linarith
    · simp [hn, hs] at h

theorem complete_result :
    sourceChecked = true ∧ programSupported [] selectedAST = true ∧
    executeObserved round64 selectedAST = some (q, helperEvents) ∧
    (∀ e ∈ helperEvents, (e.name = "exp_small" ∧
      |(e.out : ℝ) - Real.exp (e.arg : ℝ)| ≤ (2 : ℝ) / 10 ^ 11) ∨
      (e.name = "sqrt_fixed" ∧
      |(e.out : ℝ) - Real.sqrt (e.arg : ℝ)| ≤ (11 : ℝ) / 10 ^ 15)) ∧
    executeBits = some outputBits ∧ ExecC selectedAST q ∧ finiteBits outputBits = true ∧
    executeWith some selectedAST = some idealQ ∧
    |constantTarget - exactTarget| ≤ (E_constants : ℝ) ∧
    |(idealQ : ℝ) - constantTarget| ≤ (E_approximation : ℝ) ∧
    |q - idealQ| ≤ E_roundoff ∧
    |(q : ℝ) - FKS2Numerics.v1.nuAsympE30| ≤ (E : ℝ) ∧
    (0 : Rat) ≤ E ∧ E ≤ 1 / 10 ^ 12 ∧ q + E ≤ Bpoc := by
  exact ⟨source_checked, lexical_support_checked, observed_execution, reachable_helper_error,
    fixed_bits, source_refines_fp fixed_execution, output_finite, ideal_execution, constants_error,
    approximation_error, roundoff_certificate, budget_forward_error,
    rational_certificate.2.2.1, rational_certificate.2.2.2.1, rational_certificate.2.2.2.2.1⟩

end FKS2Scalar
