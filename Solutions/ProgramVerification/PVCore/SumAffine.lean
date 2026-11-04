/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVCore.Source
import SumStability.Result
import FKS2Table4.Rounding

/-!
# Shared execution model, instance checker and error theorem for `PVCore.Program`

This file is written once and used by every provider of the "sum, scale, signed constants" shape.

* `Exec src p initial out` is the operational meaning of running the selected file `src` as `p`:
  the file token-matches `p`; the literals load as binary64 values; the frozen `sum` loop runs
  under `SumStability.ExecC`; and every later multiplication, addition or subtraction is an IEEE
  round-to-nearest-even step (`SuffixIEEE`). It has no accuracy field and no expected output.
* `exact_le_out` is the error theorem: for nonnegative scale, the exact value
  `scale · Σ xᵢ ± c₁ ± …` is at most the computed output plus `forwardError`. It consumes
  `SumStability.c_sum_forward_error`, the existing proved bound
  `|ŝ - Σ xᵢ| ≤ γ_{n-1} Σ |xᵢ|`, and adds the suffix rounding error `eps`.
* `check` is an executable certificate for one instance. `certified` derives the execution, the
  domain and the error bound from `check … = true` by kernel-checked proofs.

Hypotheses inherited from `SumStability`, stated where they are used: `1 ≤ n ≤ 64` array
entries, each a binary64 value in `[2⁻⁴⁰, 1]`. Under these the loop stays in the normal range, so
no underflow or overflow occurs. The suffix steps are certified only when every intermediate is
a positive normal value with exponent in `[-100, 100]` (`FKS2Table4.additionCheck`); otherwise
`check` returns `false`. Nothing here generalizes the rounding lemmas of `SumStability`.
-/

namespace PVCore

open SumStability (RN64 Binary64 ValidInputs gamma u low CState RepresentsInput ExecC
  selectedSumProgram c_sum_forward_error sumAbs_eq_sum gamma_den gamma_nonneg)
open FKS2Scalar (decimal round64)

/-! ## Loading and evaluating -/

/-- A C decimal literal, as the binary64 value round-to-nearest gives it. -/
def loadLiteral (s : String) : Option ℚ := (decimal s).bind round64

/-- The signed constants of `p`, loaded. -/
def loadOps (p : Program) : Option (List (Sign × ℚ)) :=
  p.ops.mapM fun o => (loadLiteral o.2).map fun c => (o.1, c)

/-- Evaluator of the loop: one binary64 addition per entry, starting from `s`. -/
def runSum : List ℚ → ℚ → Option ℚ
  | [], s => some s
  | x :: xs, s => do let r ← round64 (s + x); runSum xs r

/-- Evaluator of the signed constants, starting from `r`. -/
def runOps : List (Sign × ℚ) → ℚ → Option ℚ
  | [], r => some r
  | o :: os, r => do let r' ← round64 (o.1.apply r o.2); runOps os r'

/-- Evaluator of everything after the loop: scaling, then the signed constants. -/
def runSuffix (p : Program) (s : ℚ) : Option ℚ := do
  let scale ← loadLiteral p.scale
  let ops ← loadOps p
  let r ← round64 (s * scale)
  runOps ops r

/-! ## Operational semantics -/

/-- The signed constants under IEEE round-to-nearest-even, one rounding per operation. -/
inductive OpsIEEE : List (Sign × ℚ) → ℚ → ℚ → Prop
  | nil (r : ℚ) : OpsIEEE [] r r
  | cons {σ : Sign} {c r r' out : ℚ} {os : List (Sign × ℚ)} :
      RN64 (σ.apply r c) r' → OpsIEEE os r' out → OpsIEEE ((σ, c) :: os) r out

/-- Every operation after the loop, as IEEE rounding steps. These are facts about the operations,
not error allowances. -/
def SuffixIEEE (p : Program) (s out : ℚ) : Prop :=
  ∃ scale ops r0, loadLiteral p.scale = some scale ∧ loadOps p = some ops ∧
    RN64 (s * scale) r0 ∧ OpsIEEE ops r0 out

/-- Running the selected file `src` as the program `p`, from the C state `initial`, returns `out`. -/
def Exec (src : String) (p : Program) (initial : CState) (out : ℚ) : Prop :=
  sourceMatches src p = true ∧ 1 ≤ p.inputs.length ∧ p.inputs.length ≤ 64 ∧
  ∃ xs s final, p.inputs.mapM loadLiteral = some xs ∧ RepresentsInput initial xs ∧
    runSum xs 0 = some s ∧ ExecC selectedSumProgram initial final s ∧
    runSuffix p s = some out ∧ SuffixIEEE p s out

/-! ## The exact value and the error bound -/

/-- The signed constants applied exactly, starting from `r`. -/
def opsValue : List (Sign × ℚ) → ℚ → ℚ
  | [], r => r
  | o :: os, r => opsValue os (o.1.apply r o.2)

/-- The sum of the signed constants. -/
def opsConst : List (Sign × ℚ) → ℚ
  | [] => 0
  | o :: os => (match o.1 with | .plus => o.2 | .minus => -o.2) + opsConst os

theorem opsValue_eq (os : List (Sign × ℚ)) (r : ℚ) : opsValue os r = r + opsConst os := by
  induction os generalizing r with
  | nil => simp [opsValue, opsConst]
  | cons o os ih =>
    obtain ⟨σ, c⟩ := o
    cases σ <;> simp [opsValue, opsConst, ih, Sign.apply] <;> ring

/-- What the program computes in exact arithmetic when the loop's input sum is `x`. -/
def exactValue (scale : ℚ) (os : List (Sign × ℚ)) (x : ℚ) : ℚ := opsValue os (scale * x)

/-- The proved error allowance: the loop's `γ_{n-1}` term, scaled, plus the suffix error `eps`. -/
def forwardError (scale s eps : ℚ) (n : ℕ) : ℚ := scale * (s / (1 - gamma (n - 1)) - s) + eps

theorem gamma_lt_one {k : ℕ} (hk : k ≤ 64) : gamma k < 1 := by
  have hd := gamma_den hk
  have hc : (k : ℚ) ≤ 64 := by exact_mod_cast hk
  rw [gamma, div_lt_one hd]
  norm_num [u]
  linarith

/-- The checked loop result determines the exact input sum from above. -/
theorem sum_le_of_exec {xs : List ℚ} {initial final : CState} {s : ℚ}
    (hn : 1 ≤ xs.length ∧ xs.length ≤ 64) (hd : ValidInputs xs) (hrep : RepresentsInput initial xs)
    (hk : ExecC selectedSumProgram initial final s) :
    xs.sum ≤ s / (1 - gamma (xs.length - 1)) := by
  have herr := c_sum_forward_error xs initial final s hn hd hrep hk
  rw [sumAbs_eq_sum hd] at herr
  have hg := gamma_lt_one (show xs.length - 1 ≤ 64 by omega)
  have hlo := (abs_le.mp herr).1
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- The checked loop result determines the exact input sum from below. -/
theorem sum_ge_of_exec {xs : List ℚ} {initial final : CState} {s : ℚ}
    (hn : 1 ≤ xs.length ∧ xs.length ≤ 64) (hd : ValidInputs xs) (hrep : RepresentsInput initial xs)
    (hk : ExecC selectedSumProgram initial final s) :
    s / (1 + gamma (xs.length - 1)) ≤ xs.sum := by
  have herr := c_sum_forward_error xs initial final s hn hd hrep hk
  rw [sumAbs_eq_sum hd] at herr
  have hg := gamma_nonneg (show xs.length - 1 ≤ 64 by omega)
  have hhi := (abs_le.mp herr).2
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- Unpacks an execution: the loaded inputs, loop result and output are the evaluator's. -/
theorem exec_values {src : String} {p : Program} {initial : CState} {out : ℚ}
    {xs : List ℚ} {s q : ℚ} (he : Exec src p initial out)
    (hl : p.inputs.mapM loadLiteral = some xs) (hr : runSum xs 0 = some s)
    (hq : runSuffix p s = some q) :
    out = q ∧ RepresentsInput initial xs ∧ ∃ final, ExecC selectedSumProgram initial final s := by
  obtain ⟨_, _, _, ys, v, final, hy, hrep, hv, hk, hout, _⟩ := he
  have hys : ys = xs := Option.some.inj (hy.symm.trans hl)
  subst ys
  have hvv : v = s := Option.some.inj (hv.symm.trans hr)
  subst v
  exact ⟨Option.some.inj (hout.symm.trans hq), hrep, final, hk⟩

/-- **Error theorem (upper).** The exact value of the program at the exact input sum is at most
the computed output plus `forwardError`. Hypotheses: an execution; the evaluator's loaded values;
the input domain of `SumStability`; a nonnegative scale; and the suffix rounding error `eps`. -/
theorem exact_le_out {src : String} {p : Program} {initial : CState} {out : ℚ}
    {xs : List ℚ} {s q scale eps : ℚ} {os : List (Sign × ℚ)}
    (he : Exec src p initial out) (hl : p.inputs.mapM loadLiteral = some xs)
    (hr : runSum xs 0 = some s) (hq : runSuffix p s = some q)
    (hn : 1 ≤ xs.length ∧ xs.length ≤ 64) (hd : ValidInputs xs) (h0 : 0 ≤ scale)
    (hf : |q - exactValue scale os s| ≤ eps) :
    exactValue scale os xs.sum ≤ out + forwardError scale s eps xs.length := by
  obtain ⟨hout, hrep, final, hk⟩ := exec_values he hl hr hq
  have hsum := sum_le_of_exec hn hd hrep hk
  have hm := mul_le_mul_of_nonneg_left hsum h0
  have hfl := (abs_le.mp hf).1
  rw [hout]
  simp only [exactValue, opsValue_eq, forwardError] at hfl ⊢
  linarith

/-- Lower-direction error allowance. -/
def forwardErrorLower (scale s eps : ℚ) (n : ℕ) : ℚ := scale * (s - s / (1 + gamma (n - 1))) + eps

/-- **Error theorem (lower).** The computed output minus `forwardErrorLower` is at most the exact
value. Same hypotheses as `exact_le_out`. -/
theorem out_le_exact {src : String} {p : Program} {initial : CState} {out : ℚ}
    {xs : List ℚ} {s q scale eps : ℚ} {os : List (Sign × ℚ)}
    (he : Exec src p initial out) (hl : p.inputs.mapM loadLiteral = some xs)
    (hr : runSum xs 0 = some s) (hq : runSuffix p s = some q)
    (hn : 1 ≤ xs.length ∧ xs.length ≤ 64) (hd : ValidInputs xs) (h0 : 0 ≤ scale)
    (hf : |q - exactValue scale os s| ≤ eps) :
    out - forwardErrorLower scale s eps xs.length ≤ exactValue scale os xs.sum := by
  obtain ⟨hout, hrep, final, hk⟩ := exec_values he hl hr hq
  have hsum := sum_ge_of_exec hn hd hrep hk
  have hm := mul_le_mul_of_nonneg_left hsum h0
  have hfl := (abs_le.mp hf).2
  rw [hout]
  simp only [exactValue, opsValue_eq, forwardErrorLower] at hfl ⊢
  linarith

/-! ## Executable certificate -/

/-- Each loop addition rounds correctly (`additionCheck` certifies one RN64 step). -/
def chainCheck : List ℚ → ℚ → ℚ → Bool
  | [], s, out => s == out
  | x :: xs, s, out =>
    match round64 (s + x) with
    | none => false
    | some r => FKS2Table4.additionCheck (s + x) r && chainCheck xs r out

/-- Each signed-constant step rounds correctly. -/
def opsCheck : List (Sign × ℚ) → ℚ → ℚ → Bool
  | [], r, out => r == out
  | o :: os, r, out =>
    match round64 (o.1.apply r o.2) with
    | none => false
    | some r' => FKS2Table4.additionCheck (o.1.apply r o.2) r' && opsCheck os r' out

theorem chain_sound (xs : List ℚ) (s out : ℚ) (h : chainCheck xs s out = true) :
    FKS2SumBridge.SumRun xs s out ∧ runSum xs s = some out := by
  induction xs generalizing s with
  | nil =>
    have he : s = out := by simpa [chainCheck] using h
    subst out
    exact ⟨.nil _, rfl⟩
  | cons x xs ih =>
    unfold chainCheck at h
    split at h
    · contradiction
    · rename_i r hround
      simp only [Bool.and_eq_true] at h
      obtain ⟨hrun, hev⟩ := ih r h.2
      exact ⟨.cons (FKS2Table4.additionCheck_sound h.1) hrun, by simp [runSum, hround, hev]⟩

theorem ops_sound (os : List (Sign × ℚ)) (r out : ℚ) (h : opsCheck os r out = true) :
    OpsIEEE os r out ∧ runOps os r = some out := by
  induction os generalizing r with
  | nil =>
    have he : r = out := by simpa [opsCheck] using h
    subst out
    exact ⟨.nil _, rfl⟩
  | cons o os ih =>
    obtain ⟨σ, c⟩ := o
    unfold opsCheck at h
    split at h
    · contradiction
    · rename_i r' hround
      simp only [Bool.and_eq_true] at h
      obtain ⟨hrun, hev⟩ := ih r' h.2
      exact ⟨.cons (FKS2Table4.additionCheck_sound h.1) hrun, by simp [runOps, hround, hev]⟩

/-- The initial C state of the selected call `sum(inputs, n)`, with the array at address 4096. -/
abbrev initialFor (xs : List ℚ) : CState := FKS2SumBridge.sumInitial xs

theorem represents_initial {xs : List ℚ} (h : xs.length ≤ 64) :
    RepresentsInput (initialFor xs) xs := by
  refine ⟨rfl, rfl, rfl, by simp [FKS2SumBridge.sumInitial], ?_, by simp [FKS2SumBridge.sumInitial]⟩
  change 4096 + 8 * xs.length < 2 ^ 64
  have : 4096 + 8 * xs.length ≤ 4096 + 8 * 64 := by omega
  exact lt_of_le_of_lt this (by norm_num)

theorem kernel_from_chain {xs : List ℚ} {s : ℚ}
    (hc : chainCheck xs 0 s = true) (hn : xs.length ≤ 64) :
    ∃ final, ExecC selectedSumProgram (initialFor xs) final s := by
  have hrun := (chain_sound xs 0 s hc).1
  obtain ⟨last, hl, hout⟩ := FKS2SumBridge.run_to_for hrun (initialFor xs) rfl
    (by simp [FKS2SumBridge.sumInitial]) rfl (by simp [FKS2SumBridge.sumInitial]) hn
  refine ⟨{ last with returned := some last.acc }, rfl, last, ?_, rfl, hout.symm⟩
  simpa [SumStability.initialized, FKS2SumBridge.sumInitial] using hl

/-- The values an instance computes: loaded inputs, loop result, loaded scale and constants,
scaled value and output. -/
structure Values where
  xs : List ℚ
  s : ℚ
  scale : ℚ
  ops : List (Sign × ℚ)
  r0 : ℚ
  out : ℚ
  deriving Inhabited, Repr

def values? (p : Program) : Option Values := do
  let xs ← p.inputs.mapM loadLiteral
  let s ← runSum xs 0
  let scale ← loadLiteral p.scale
  let ops ← loadOps p
  let r0 ← round64 (s * scale)
  let out ← runOps ops r0
  return ⟨xs, s, scale, ops, r0, out⟩

/-- The evaluated values of `p` (meaningful when `check` passes). -/
def valuesOf (p : Program) : Values := (values? p).getD default

/-- **Instance certificate.** Every conjunct is finite rational arithmetic on the actual file and
literals. `eps` is the suffix rounding allowance the instance claims. -/
def check (src : String) (p : Program) (eps : ℚ) : Bool :=
  match values? p with
  | none => false
  | some v =>
    sourceMatches src p && decide (1 ≤ p.inputs.length) && decide (p.inputs.length ≤ 64) &&
    v.xs.all FKS2SumBridge.inputCheck && chainCheck v.xs 0 v.s &&
    FKS2Table4.additionCheck (v.s * v.scale) v.r0 && opsCheck v.ops v.r0 v.out &&
    decide (0 ≤ v.scale) && decide (|v.out - exactValue v.scale v.ops v.s| ≤ eps)

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by simp at h; subst h; rfl
  | a :: as, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨b, _, bs, hbs, hl'⟩ := h
    simp only [Option.pure_def, Option.some.injEq] at hl'
    subst hl'
    simp [mapM_length hbs]

/-- **Soundness of the certificate.** From `check src p eps = true`, kernel-checked proofs give the
execution of the actual file, the input domain and the error bound, for the evaluated values. -/
theorem certified {src : String} {p : Program} {eps : ℚ} (h : check src p eps = true) :
    let v := valuesOf p
    Exec src p (initialFor v.xs) v.out ∧ ValidInputs v.xs ∧
    (1 ≤ v.xs.length ∧ v.xs.length ≤ 64) ∧ 0 ≤ v.scale ∧
    exactValue v.scale v.ops v.xs.sum ≤ v.out + forwardError v.scale v.s eps v.xs.length ∧
    v.out - forwardErrorLower v.scale v.s eps v.xs.length ≤ exactValue v.scale v.ops v.xs.sum := by
  unfold check at h
  split at h
  · contradiction
  rename_i v hv
  have hvo : valuesOf p = v := by simp [valuesOf, hv]
  simp only [hvo]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsrc, hn1⟩, hn2⟩, hdom⟩, hchain⟩, hscale⟩, hops⟩, h0⟩, hf⟩ := h
  -- unpack the evaluator
  simp only [values?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hv
  obtain ⟨xs, hxs, s, hs, scale, hsc, os, hos, r0, hr0, out, hout, hvv⟩ := hv
  subst hvv
  simp only at hsrc hn1 hn2 hdom hchain hscale hops h0 hf ⊢
  have hlen : xs.length = p.inputs.length := mapM_length hxs
  have hn : 1 ≤ xs.length ∧ xs.length ≤ 64 := ⟨by omega, by omega⟩
  have hd : ValidInputs xs := fun r hr => FKS2SumBridge.inputCheck_sound (hdom r hr)
  have hrep := represents_initial (xs := xs) hn.2
  obtain ⟨final, hk⟩ := kernel_from_chain hchain hn.2
  have hrun := (chain_sound xs 0 s hchain).2
  have hopsS := ops_sound os r0 out hops
  have hq : runSuffix p s = some out := by
    simp [runSuffix, hsc, hos, hr0, hopsS.2]
  have hsuffix : SuffixIEEE p s out :=
    ⟨scale, os, r0, hsc, hos, FKS2Table4.additionCheck_sound hscale, hopsS.1⟩
  have he : Exec src p (initialFor xs) out :=
    ⟨hsrc, hn1, hn2, xs, s, final, hxs, hrep, hrun, hk, hq, hsuffix⟩
  exact ⟨he, hd, hn, h0, exact_le_out he hxs hrun hq hn hd h0 hf,
    out_le_exact he hxs hrun hq hn hd h0 hf⟩

/-- An execution of a checked program returns exactly the evaluated output. -/
theorem output_unique {src : String} {p : Program} {eps : ℚ} (h : check src p eps = true)
    {initial : CState} {out : ℚ} (he : Exec src p initial out) : out = (valuesOf p).out := by
  unfold check at h
  split at h
  · contradiction
  rename_i v hv
  have hvo : valuesOf p = v := by simp [valuesOf, hv]
  rw [hvo]
  simp only [values?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hv
  obtain ⟨xs, hxs, s, hs, scale, hsc, os, hos, r0, hr0, out', hout, hvv⟩ := hv
  subst hvv
  have hq : runSuffix p s = some out' := by simp [runSuffix, hsc, hos, hr0, hout]
  exact (exec_values he hxs hs hq).1

end PVCore
