/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityCachedSum
import Mathlib.Tactic

open LeanCert.Core LeanCert.Engine
namespace WinnerProgramA

abbrev lit := Expr.const
abbrev add := Expr.add
abbrev mul := Expr.mul
def sub (a b : Expr) := add a (.neg b)
def divE (a b : Expr) := mul a (.inv b)
def powE (a : Expr) : Nat → Expr
  | 0 => lit 1
  | n + 1 => mul a (powE a n)

def moment (s : Expr) (c d : ℚ) : Expr :=
  let h := Expr.log (lit 3000000000000)
  let a := divE (sub (mul (lit 8) s) (lit 5)) (lit 3)
  let q := sub (lit 5) (mul (lit 2) s)
  let u := mul a h
  let f1 := q
  let f2 := mul f1 (sub q (lit 1))
  let f3 := mul f2 (sub q (lit 2))
  let f4 := mul f3 (sub q (lit 3))
  let poly := add (add (add (add (lit 1) (divE f1 u))
    (divE f2 (powE u 2))) (divE f3 (powE u 3))) (divE f4 (powE u 4))
  add (divE (mul (mul (lit c) (Expr.exp (add (.neg (mul a h))
      (mul q (Expr.log h))))) poly) a)
    (mul (lit (d / 3000000000000)) (add (add (powE h 2) (mul (lit 2) h)) (lit 2)))

structure Row where
  body : Expr
  cells : Nat

def rightRow (a : ℚ) (n den : Nat) (c d : ℚ) : Row :=
  let step : ℚ := 1 / den
  let left := add (lit a) (mul (lit step) (.var 0))
  let right := add left (lit step)
  ⟨mul (lit (600 * step)) (mul (Expr.exp (mul (lit 300) (sub right (lit (7/8)))))
    (moment left c d)), n⟩

def chordRow (a : ℚ) (n den : Nat) (c d : ℚ) : Row :=
  let step : ℚ := 1 / den
  let left := add (lit a) (mul (lit step) (.var 0))
  let right := add left (lit step)
  let e := Expr.exp (mul (lit 300) (sub left (lit (7/8))))
  let z : ℚ := 300 * step
  let mass := mul e (divE (sub (Expr.exp (lit z)) (lit 1)) (lit 300))
  let wb := mul e (divE (add (mul (Expr.exp (lit z)) (lit (z-1))) (lit 1))
    (lit (90000 * step)))
  let wa := sub mass wb
  ⟨mul (lit 600) (add (mul wa (moment left c d)) (mul wb (moment right c d))), n⟩

def remainder : Row :=
  let z := sub (lit 150) (Expr.log (lit 4))
  let low := mul (lit 2) (mul (Expr.exp (lit (-105/2)))
    (add (add (add (lit 1) z) (divE (powE z 2) (lit 2)))
      (moment (lit (7/10)) (64369/10000) (44648/10000))))
  ⟨add low (mul (lit 7800) (Expr.exp (lit (-225/2)))), 1⟩

def p0 : List Row := [
  rightRow (7/10) 10000 100000 (64369/10000) (44648/10000),
  rightRow (8/10) 1000 100000 (67949/10000) (36554/10000),
  rightRow (81/100) 1000 100000 (71697/10000) (35762/10000),
  rightRow (82/100) 1000 100000 (75617/10000) (34971/10000),
  rightRow (83/100) 1000 100000 (79713/10000) (34179/10000),
  rightRow (84/100) 1000 100000 (83991/10000) (33387/10000),
  rightRow (85/100) 1000 100000 (88453/10000) (32594/10000),
  rightRow (86/100) 1000 100000 (93103/10000) (31801/10000),
  rightRow (87/100) 500 100000 (97945/10000) (31008/10000), remainder]

def p1 : List Row := [
  chordRow (7/10) 1600 16000 (64369/10000) (44648/10000),
  chordRow (8/10) 160 16000 (67949/10000) (36554/10000),
  chordRow (81/100) 160 16000 (71697/10000) (35762/10000),
  chordRow (82/100) 160 16000 (75617/10000) (34971/10000),
  chordRow (83/100) 160 16000 (79713/10000) (34179/10000),
  chordRow (84/100) 160 16000 (83991/10000) (33387/10000),
  chordRow (85/100) 160 16000 (88453/10000) (32594/10000),
  chordRow (86/100) 160 16000 (93103/10000) (31801/10000),
  chordRow (87/100) 80 16000 (97945/10000) (31008/10000), remainder]

def cfg : DyadicConfig := { precision := -100, taylorDepth := 24 }
def runRow (r : Row) : IntervalDyadic × Bool :=
  CH2QRH.DensityComputation.checkedSumAux r.body 0 (r.cells - 1) finSumZero
    (LeanCert.Internal.Dyadic.prepareContext cfg)
def run (p : List Row) := p.map runRow
/-- Execution is exact interval-program evaluation, with no accuracy/result premise. -/
def Exec (p : List Row) (out : List (IntervalDyadic × Bool)) : Prop := out = run p
noncomputable def rowValue (r : Row) : ℝ :=
  ∑ k ∈ Finset.Icc 0 (r.cells - 1), Expr.eval (sumBodyRealEnv k) r.body
noncomputable def value (p : List Row) : ℝ := (p.map rowValue).sum

def acceptUpper : List (IntervalDyadic × Bool) → List ℚ → Bool
  | [], [] => true
  | v::vs, b::bs => (v.2 && v.1.upperBoundedBy b) && acceptUpper vs bs
  | _, _ => false

def acceptLower : List (IntervalDyadic × Bool) → List ℚ → Bool
  | [], [] => true
  | v::vs, b::bs => (v.2 && v.1.lowerBoundedBy b) && acceptLower vs bs
  | _, _ => false

theorem source_linked_upper (p : List Row) (out : List (IntervalDyadic × Bool))
    (bs : List ℚ) (hex : Exec p out) (h : acceptUpper out bs = true) :
    value p ≤ ((bs.sum : ℚ) : ℝ) := by
  subst out
  induction p generalizing bs with
  | nil => cases bs <;> simp_all [run, acceptUpper, value]
  | cons r rs ih =>
    cases bs with
    | nil => simp [run, acceptUpper] at h
    | cons b bs =>
      have hh : (((runRow r).2 && (runRow r).1.upperBoundedBy b) = true) ∧
          (acceptUpper (run rs) bs = true) := by simpa [run, acceptUpper] using h
      have hr : rowValue r ≤ (b : ℝ) := by
        apply CH2QRH.DensityComputation.verify_upper r.body 0 (r.cells-1) b cfg (by decide)
        exact hh.1
      have ht := ih bs hh.2
      simp only [value, List.map_cons, List.sum_cons, Rat.cast_add] at *
      linarith

/-- Cached lower acceptance is identical to the original pinned lower checker. -/
theorem cached_lower (r : Row) (b : ℚ)
    (h : ((runRow r).2 && (runRow r).1.lowerBoundedBy b) = true) :
    (b : ℝ) ≤ rowValue r := by
  apply verify_finsum_lower_full_checked r.body 0 (r.cells-1) b cfg (by decide)
  simpa only [runRow, CH2QRH.DensityComputation.checkedSumAux_fst,
    CH2QRH.DensityComputation.checkedSumAux_snd, checkFinSumLowerBoundFull,
    checkDomainValidAll, checkFinSumLowerBound, finSumDyadic] using h

theorem source_linked_lower (p : List Row) (out : List (IntervalDyadic × Bool))
    (bs : List ℚ) (hex : Exec p out) (h : acceptLower out bs = true) :
    ((bs.sum : ℚ) : ℝ) ≤ value p := by
  subst out
  induction p generalizing bs with
  | nil => cases bs <;> simp_all [run, acceptLower, value]
  | cons r rs ih =>
    cases bs with
    | nil => simp [run, acceptLower] at h
    | cons b bs =>
      have hh : (((runRow r).2 && (runRow r).1.lowerBoundedBy b) = true) ∧
          (acceptLower (run rs) bs = true) := by simpa [run, acceptLower] using h
      have hr := cached_lower r b hh.1
      have ht := ih bs hh.2
      simp only [value, List.map_cons, List.sum_cons, Rat.cast_add] at *
      linarith

#print axioms source_linked_upper
#print axioms source_linked_lower
end WinnerProgramA
