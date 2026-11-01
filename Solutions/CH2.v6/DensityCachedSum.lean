/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LeanCert.Engine.FinSumDyadic

open LeanCert.Core LeanCert.Engine
namespace CH2QRH.DensityComputation

/-- Compute the enclosure and its domain flag together, sharing prepared Taylor data. -/
def checkedSumAux (body : Expr) (current limit : Nat) (acc : IntervalDyadic)
    (ctx : LeanCert.Internal.Dyadic.PreparedContext) : IntervalDyadic × Bool :=
  if current > limit then (acc, true)
  else
    let term := LeanCert.Internal.Dyadic.evalPreparedCached body
      (sumBodyEnvSimple current ctx.cfg.precision) ctx
    let next := (IntervalDyadic.add acc term.1).roundOut ctx.cfg.precision
    let rest := checkedSumAux body (current + 1) limit next ctx
    (rest.1, term.2 && rest.2)
  termination_by limit + 1 - current

/-- This computes exactly the original verified enclosure, without changing its arithmetic. -/
theorem checkedSumAux_fst (body : Expr) (current limit : Nat) (acc : IntervalDyadic)
    (cfg : DyadicConfig) :
    (checkedSumAux body current limit acc (LeanCert.Internal.Dyadic.prepareContext cfg)).1 =
      finSumAux body current limit acc cfg := by
  generalize hm : limit + 1 - current = m
  induction m using Nat.strongRecOn generalizing current acc with
  | ind m ih =>
    rw [checkedSumAux, finSumAux]
    split_ifs with h
    · rfl
    · dsimp only
      simp only [LeanCert.Internal.Dyadic.prepareContext_cfg]
      rw [evalIntervalDyadicPreparedCached_fst body (sumBodyEnvSimple current cfg.precision) cfg]
      exact ih (limit + 1 - (current + 1)) (by omega) (current + 1) _ rfl

/-- This checks exactly the original domain conditions at every index. -/
theorem checkedSumAux_snd (body : Expr) (current limit : Nat) (acc : IntervalDyadic)
    (cfg : DyadicConfig) :
    (checkedSumAux body current limit acc (LeanCert.Internal.Dyadic.prepareContext cfg)).2 =
      checkDomainValidAllAux body current limit cfg := by
  generalize hm : limit + 1 - current = m
  induction m using Nat.strongRecOn generalizing current acc with
  | ind m ih =>
    rw [checkedSumAux, checkDomainValidAllAux]
    split_ifs with h
    · rfl
    · dsimp only
      simp only [LeanCert.Internal.Dyadic.prepareContext_cfg]
      rw [evalIntervalDyadicPreparedCached_snd body (sumBodyEnvSimple current cfg.precision) cfg]
      rw [ih (limit + 1 - (current + 1)) (by omega) (current + 1) _ rfl]

/-- A shared evaluation route for the same combined finite-sum certificate. -/
def checkUpperBound (body : Expr) (a b : Nat) (target : ℚ) (cfg : DyadicConfig) : Bool :=
  let result := checkedSumAux body a b finSumZero (LeanCert.Internal.Dyadic.prepareContext cfg)
  result.2 && result.1.upperBoundedBy target

/-- The new computation has precisely the same acceptance predicate as the pinned checker. -/
theorem checkUpperBound_eq (body : Expr) (a b : Nat) (target : ℚ) (cfg : DyadicConfig) :
    checkUpperBound body a b target cfg = checkFinSumUpperBoundFull body a b target cfg := by
  simp only [checkUpperBound, checkedSumAux_fst, checkedSumAux_snd,
    checkFinSumUpperBoundFull, checkDomainValidAll, checkFinSumUpperBound, finSumDyadic]

/-- Reuse the unchanged pinned soundness theorem after the proved computation equality. -/
theorem verify_upper (body : Expr) (a b : Nat) (target : ℚ) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0) (hcheck : checkUpperBound body a b target cfg = true) :
    ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤ target := by
  apply verify_finsum_upper_full_checked body a b target cfg hprec
  simpa only [checkUpperBound_eq] using hcheck

end CH2QRH.DensityComputation
#print axioms CH2QRH.DensityComputation.verify_upper
