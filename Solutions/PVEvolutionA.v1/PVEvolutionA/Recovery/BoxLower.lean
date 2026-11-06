/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- Finite box evaluator wrapper; all real soundness uses the existing engine. -/
import PVEvolutionA.Fast
namespace PVEvolutionA.Recovery.BoxLower
open LeanCert.Core LeanCert.Engine
set_option maxHeartbeats 0

def cfg : DyadicConfig := { precision := -80, taylorDepth := 16 }
def output (e : Expr) (I : IntervalRat) : IntervalDyadic × Bool :=
  LeanCert.Internal.Dyadic.evalPreparedCached e
    (fun _ => IntervalDyadic.ofIntervalRat I cfg.precision)
    (LeanCert.Internal.Dyadic.prepareContext cfg)
def accepted (e : Expr) (I : IntervalRat) (q : ℚ) : Bool :=
  (output e I).2 && (output e I).1.lowerBoundedBy q

theorem sound {e : Expr} {I : IntervalRat} {q : ℚ}
    (h : accepted e I q = true) {x : ℝ} (hx : x ∈ I) :
    (q : ℝ) ≤ Expr.eval (fun _ => x) e := by
  have hs : (output e I).2 = true ∧ (output e I).1.lowerBoundedBy q = true :=
    by simpa only [accepted, Bool.and_eq_true] using h
  have hd : checkDomainValidDyadic e
      (fun _ => IntervalDyadic.ofIntervalRat I cfg.precision) cfg = true := by
    simpa only [output, evalIntervalDyadicPreparedCached_snd] using hs.1
  have hm := evalIntervalDyadic_correct_of_domain e (fun _ => x)
    (fun _ => IntervalDyadic.ofIntervalRat I cfg.precision)
    (fun _ => IntervalDyadic.mem_ofIntervalRat hx cfg.precision (by decide)) cfg
    (by decide) (checkDomainValidDyadic_correct e _ cfg hd)
  have hm' : Expr.eval (fun _ => x) e ∈ (output e I).1 := by
    simpa only [output, evalIntervalDyadicPreparedCached_fst] using hm
  exact (IntervalDyadic.lowerBoundedBy_spec hs.2).trans
    (IntervalDyadic.lo_le_of_mem hm')
#print axioms sound
end PVEvolutionA.Recovery.BoxLower
