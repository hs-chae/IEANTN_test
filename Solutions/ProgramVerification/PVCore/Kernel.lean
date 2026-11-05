/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVCore.SumAffine
import PVCore.Bridge

/-!
# Kernel route: the certificate with one native fact, for decoding only

`check` is one Boolean computation, and an instance proves it with one `native_decide`: the
compiled evaluator, not the kernel, runs everything in it. Almost all of it is finite rational
arithmetic the kernel can reduce itself — token matching of the source, the binary64 loop and its
rounding chain, the suffix certificate. One part is not: decoding the decimal literals
(`FKS2Scalar.decimal` goes through `String.splitOn` and `String.toNat?`, which the kernel does not
reduce). This is the trust-reduction recipe of the calibration pilot (`CalibrationPilot.KernelA`),
made generic:

* `decode p = some (xs, scale, ops)`: the literals as rationals. **The one native fact.**
* `checkFrom src p eps xs scale ops = true`: every other conjunct of `check`, on those rationals.
  **Kernel-checked** (`decide +kernel`).
* `check_of_decode`: together they give `check src p eps = true`, so `certified` and every family
  theorem apply unchanged.

The kernel computation is slower and larger than the native one (measured per instance in
`docs/program-verification/PV_TEST_AND_REPLAY_LOG.md`); the trusted computation shrinks to parsing.
-/

namespace PVCore

open FKS2Scalar (round64)

/-- Literal decoding alone: the only part of `check` that needs `String → ℚ` parsing. -/
def decode (p : Program) : Option (List ℚ × ℚ × List (Sign × ℚ)) := do
  let xs ← p.inputs.mapM loadLiteral
  let scale ← loadLiteral p.scale
  let ops ← loadOps p
  return (xs, scale, ops)

/-- The evaluated values, from decoded literals: no parsing. -/
def valuesFrom (xs : List ℚ) (scale : ℚ) (ops : List (Sign × ℚ)) : Option Values := do
  let s ← runSum xs 0
  let r0 ← round64 (s * scale)
  let out ← runOps ops r0
  return ⟨xs, s, scale, ops, r0, out⟩

/-- The conjuncts of `check` on given values. -/
def checkWith (src : String) (p : Program) (eps : ℚ) (v : Values) : Bool :=
  sourceMatches src p && decide (1 ≤ p.inputs.length) && decide (p.inputs.length ≤ 64) &&
    v.xs.all FKS2SumBridge.inputCheck && chainCheck v.xs 0 v.s &&
    FKS2Table4.additionCheck (v.s * v.scale) v.r0 && opsCheck v.ops v.r0 v.out &&
    decide (0 ≤ v.scale) && decide (|v.out - exactValue v.scale v.ops v.s| ≤ eps)

/-- `check` without parsing: the part the kernel reduces. -/
def checkFrom (src : String) (p : Program) (eps : ℚ) (xs : List ℚ) (scale : ℚ)
    (ops : List (Sign × ℚ)) : Bool :=
  match valuesFrom xs scale ops with
  | none => false
  | some v => checkWith src p eps v

theorem values?_of_decode {p : Program} {xs : List ℚ} {scale : ℚ} {ops : List (Sign × ℚ)}
    (h : decode p = some (xs, scale, ops)) : values? p = valuesFrom xs scale ops := by
  simp only [decode, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨xs', hxs, scale', hsc, ops', hops, rfl, rfl, rfl⟩ := h
  simp [values?, valuesFrom, hxs, hsc, hops]

theorem valuesOf_of_decode {p : Program} {xs : List ℚ} {scale : ℚ} {ops : List (Sign × ℚ)}
    {v : Values} (h : decode p = some (xs, scale, ops)) (hv : valuesFrom xs scale ops = some v) :
    valuesOf p = v := by
  simp [valuesOf, values?_of_decode h, hv]

/-- **Kernel route to the certificate.** -/
theorem check_of_decode {src : String} {p : Program} {eps : ℚ} {xs : List ℚ} {scale : ℚ}
    {ops : List (Sign × ℚ)} (hd : decode p = some (xs, scale, ops))
    (hk : checkFrom src p eps xs scale ops = true) : check src p eps = true := by
  unfold checkFrom at hk
  unfold check
  rw [values?_of_decode hd]
  split at hk
  · contradiction
  · rename_i v hv
    simp only [hv]
    exact hk

theorem valuesFrom_fields {xs : List ℚ} {scale : ℚ} {ops : List (Sign × ℚ)} {v : Values}
    (h : valuesFrom xs scale ops = some v) : v.xs = xs ∧ v.scale = scale ∧ v.ops = ops := by
  simp only [valuesFrom, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨s, -, r0, -, out, -, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-- `upperCheck` on given decoded literals. -/
def upperFrom (src : String) (p : Program) (eps bound : ℚ) (xs : List ℚ) (scale : ℚ)
    (ops : List (Sign × ℚ)) : Bool :=
  match valuesFrom xs scale ops with
  | none => false
  | some v => checkWith src p eps v &&
      decide (v.out + forwardError v.scale v.s eps v.xs.length ≤ bound)

/-- **Kernel route to an upper-bound certificate**, with the decoded fields of `valuesOf p`. -/
theorem upperCheck_of_decode {src : String} {p : Program} {eps bound : ℚ} {xs : List ℚ}
    {scale : ℚ} {ops : List (Sign × ℚ)} (hd : decode p = some (xs, scale, ops))
    (hk : upperFrom src p eps bound xs scale ops = true) :
    upperCheck src p eps bound = true ∧
      (valuesOf p).xs = xs ∧ (valuesOf p).scale = scale ∧ (valuesOf p).ops = ops := by
  unfold upperFrom at hk
  split at hk
  · contradiction
  rename_i v hv
  have hvo := valuesOf_of_decode hd hv
  simp only [Bool.and_eq_true] at hk
  have hc : check src p eps = true := by
    apply check_of_decode hd
    unfold checkFrom
    rw [hv]
    exact hk.1
  refine ⟨?_, ?_⟩
  · unfold upperCheck
    rw [hvo, hc]
    simpa using hk.2
  · rw [hvo]
    exact valuesFrom_fields hv

end PVCore
