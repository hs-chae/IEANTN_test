import FKS2SumBridge.Rounding
import FKS2SumBridge.Trace
import SumStability.Result

namespace FKS2SumBridge
open FKS2Scalar SumStability

def exponentOf (x : ℚ) : ℤ :=
  let g := (x.num.natAbs.log2 : ℤ) - (x.den.log2 : ℤ)
  if x < (2 : ℚ) ^ g then g - 53 else g - 52

def mantissaOf (x : ℚ) : ℤ := ⌊x / (2 : ℚ) ^ exponentOf x⌋

def reprCheck (x : ℚ) : Bool := decide (
  |mantissaOf x| < 2 ^ 53 ∧ -1074 ≤ exponentOf x ∧ exponentOf x ≤ 971 ∧
    x = (mantissaOf x : ℚ) * (2 : ℚ) ^ exponentOf x)

theorem reprCheck_sound {x : ℚ} (h : reprCheck x = true) : Binary64 x := by
  exact ⟨mantissaOf x, exponentOf x, of_decide_eq_true h⟩

def inputCheck (x : ℚ) : Bool := reprCheck x && decide (low ≤ x ∧ x ≤ 1)

theorem inputCheck_sound {x : ℚ} (h : inputCheck x = true) :
    Binary64 x ∧ low ≤ x ∧ x ≤ 1 := by
  simp only [inputCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨reprCheck_sound h.1, h.2⟩

def addCheck (x y : ℚ) : Bool :=
  if x == y then reprCheck y
  else
    let m : ℤ := ⌊y / unit⌋
    decide (y = (m : ℚ) * unit ∧ (2 ^ 52 ≤ m ∧ m < 2 ^ 53) ∧
      (1 + unit / 2 ≤ x ∧ x ≤ 2 - unit / 2) ∧ |y - x| ≤ unit / 2 ∧
      (|y - x| = unit / 2 → Even m))

theorem addCheck_sound {x y : ℚ} (h : addCheck x y = true) : RN64 x y := by
  unfold addCheck at h
  split at h
  · rename_i he
    have heq : x = y := by simpa using he
    subst x
    exact SumStability.rn_self (reprCheck_sound h)
  · have hc := of_decide_eq_true h
    rcases hc with ⟨hy, hm, hx, he, ht⟩
    have hr := scoped_RN64 _ _ hm hx (by simpa only [← hy] using he)
      (by simpa only [← hy] using ht)
    simpa only [← hy] using hr

inductive SumRun : List ℚ → ℚ → ℚ → Prop
  | nil (s : ℚ) : SumRun [] s s
  | cons {x : ℚ} {xs : List ℚ} {s r out : ℚ} :
      RN64 (s + x) r → SumRun xs r out → SumRun (x :: xs) s out

def beforeAcc (name : String) (st : Iteration) : ℚ := (get st.before.env name).getD 0
def afterAcc (name : String) (st : Iteration) : ℚ := (get st.afterBody.env name).getD 0

def chainCheck (name : String) : List Iteration → ℚ → ℚ → Bool
  | [], start, out => start == out
  | step :: rest, start, out =>
    (beforeAcc name step == start) &&
    addCheck (start + termOf step) (afterAcc name step) &&
    chainCheck name rest (afterAcc name step) out

theorem chainCheck_sound (name : String) (steps : List Iteration) (start out : ℚ)
    (h : chainCheck name steps start out = true) :
    SumRun (steps.map termOf) start out := by
  induction steps generalizing start with
  | nil =>
    have he : start = out := by simpa [chainCheck] using h
    subst out
    exact SumRun.nil start
  | cons step rest ih =>
    simp only [chainCheck, Bool.and_eq_true] at h
    exact SumRun.cons (addCheck_sound h.1.2) (ih _ h.2)

def stepCheck (name : String) (step : Iteration) : Bool := decide (
  (eventOf step).name = "exp_small" ∧
  step.eventsAfter = eventOf step :: step.eventsBefore ∧
  get step.afterBody.env "t" = some (eventOf step).arg ∧
  round64 (beforeAcc name step + termOf step) = some (afterAcc name step) ∧
  get step.afterIncrement.env name = get step.afterBody.env name ∧
  get step.afterIncrement.env "k" = some (counterOf step + 1))

theorem concrete_trace_checks :
    trace1.steps.length = 41 ∧ trace2.steps.length = 42 ∧
    trace1.steps.map counterOf = (List.range 41).map (fun j => (j + 3 : ℕ)) ∧
    trace2.steps.map counterOf = (List.range 42).map (fun j => (j + 3 : ℕ)) ∧
    (∀ step ∈ trace1.steps, stepCheck "s1" step = true ∧ inputCheck (termOf step) = true) ∧
    (∀ step ∈ trace2.steps, stepCheck "s2" step = true ∧ inputCheck (termOf step) = true) ∧
    chainCheck "s1" trace1.steps 0 acc1 = true ∧
    chainCheck "s2" trace2.steps 0 acc2 = true ∧
    get fullFrame.env "s1" = some acc1 ∧ get fullFrame.env "s2" = some acc2 := by
  native_decide

theorem terms_lengths : terms1.length = 41 ∧ terms2.length = 42 := by
  simpa [terms1, terms2] using And.intro concrete_trace_checks.1 concrete_trace_checks.2.1

theorem terms_valid : ValidInputs terms1 ∧ ValidInputs terms2 := by
  constructor
  · intro x hx
    obtain ⟨step, hs, rfl⟩ := List.mem_map.mp hx
    exact inputCheck_sound (concrete_trace_checks.2.2.2.2.1 step hs).2
  · intro x hx
    obtain ⟨step, hs, rfl⟩ := List.mem_map.mp hx
    exact inputCheck_sound (concrete_trace_checks.2.2.2.2.2.1 step hs).2

theorem concrete_runs : SumRun terms1 0 acc1 ∧ SumRun terms2 0 acc2 := by
  exact ⟨chainCheck_sound _ _ _ _ concrete_trace_checks.2.2.2.2.2.2.1,
    chainCheck_sound _ _ _ _ concrete_trace_checks.2.2.2.2.2.2.2.1⟩

/-- Construct source-model execution from a proved ordered RN64 operation chain. -/
theorem run_to_for {xs : List ℚ} {s out : ℚ} (h : SumRun xs s out)
    (st : CState) (hs : st.acc = s) (hbuf : st.buffer.drop st.i = xs)
    (hn : st.n = st.buffer.length) (hi : st.i ≤ st.n) (hmax : st.n ≤ 64) :
    ∃ final, ForExec st final ∧ final.acc = out := by
  induction h generalizing st with
  | nil s =>
    have hb : st.buffer.length ≤ st.i := List.drop_eq_nil_iff.mp hbuf
    exact ⟨st, ForExec.done _ (by omega), hs⟩
  | @cons x xs s r out hadd hrun ih =>
    have hguard : st.i < st.n := by
      by_contra hg
      have he : st.buffer.drop st.i = [] := List.drop_eq_nil_iff.mpr (by omega)
      rw [he] at hbuf
      contradiction
    have hread : readDouble st (st.base + 8 * st.i) = some x := by
      rw [read_index]
      have hh := congrArg List.head? hbuf
      simpa using hh
    have hincr : (advance st r).i = st.i + 1 := by
      exact Nat.mod_eq_of_lt (by omega)
    have hbnext : (advance st r).buffer.drop (advance st r).i = xs := by
      change st.buffer.drop (advance st r).i = xs
      rw [hincr, ← List.drop_drop, hbuf]
      rfl
    obtain ⟨final, hf, ho⟩ := ih (advance st r) rfl hbnext hn (by
      change (advance st r).i ≤ st.n
      rw [hincr]; omega) hmax
    refine ⟨final, ForExec.step st final x r hguard hread ?_ hf, ho⟩
    simpa [hs] using hadd

def sumInitial (xs : List ℚ) : CState := ⟨xs, 4096, xs.length, xs.length, 0, 0, none⟩

theorem concrete_source_executions :
    (∃ final, RepresentsInput (sumInitial terms1) terms1 ∧
      SumStability.ExecC selectedSumProgram (sumInitial terms1) final acc1) ∧
    (∃ final, RepresentsInput (sumInitial terms2) terms2 ∧
      SumStability.ExecC selectedSumProgram (sumInitial terms2) final acc2) := by
  have build (xs : List ℚ) (out : ℚ) (hlen : xs.length ≤ 64) (hr : SumRun xs 0 out) :
      ∃ final, RepresentsInput (sumInitial xs) xs ∧
        SumStability.ExecC selectedSumProgram (sumInitial xs) final out := by
    have hh := run_to_for hr (sumInitial xs) rfl (by simp [sumInitial]) rfl (by simp [sumInitial]) hlen
    obtain ⟨last, hl, hout⟩ := hh
    refine ⟨{ last with returned := some last.acc }, ?_, rfl, last, ?_, rfl, hout.symm⟩
    · simp [RepresentsInput, sumInitial]
      omega
    · simpa [initialized, sumInitial] using hl
  exact ⟨build _ _ (by rw [terms_lengths.1]; omega) concrete_runs.1,
    build _ _ (by rw [terms_lengths.2]; omega) concrete_runs.2⟩

theorem rounding_bounds :
    |(acc1 : ℝ) - exactSum terms1| ≤ (gamma 40 : ℝ) * sumAbs terms1 ∧
    |(acc2 : ℝ) - exactSum terms2| ≤ (gamma 41 : ℝ) * sumAbs terms2 := by
  obtain ⟨final1, hrep1, hrun1⟩ := concrete_source_executions.1
  obtain ⟨final2, hrep2, hrun2⟩ := concrete_source_executions.2
  constructor
  · simpa [terms_lengths.1] using c_sum_forward_error_real terms1 _ final1 acc1
      (by rw [terms_lengths.1]; omega) terms_valid.1 hrep1 hrun1
  · simpa [terms_lengths.2] using c_sum_forward_error_real terms2 _ final2 acc2
      (by rw [terms_lengths.2]; omega) terms_valid.2 hrep2 hrun2

end FKS2SumBridge
