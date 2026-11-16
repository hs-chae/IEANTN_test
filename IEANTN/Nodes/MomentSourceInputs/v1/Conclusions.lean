/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.Zeta
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

namespace MomentSourceInputs.v1
noncomputable section

/--
Hiary (arXiv1507.01261v4), Theorem1.1 first sentence andLemma2.2: the low critical-line bound on
0 <= u <= 3.
-/
noncomputable def low_zeta : Prop :=
∀ (u : ℝ),
  (0 : ℝ) ≤ u →
    u ≤ (3 : ℝ) → ‖riemannZeta ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) (1 / 2 : ℝ) u)‖ ≤ (1461 / 1000 : ℝ)

/--
Revers (arXiv2602.05614v1), Theorem1.1(a), PDFpage3: the .611 critical-line bound for all u >=
3.
-/
noncomputable def revers_zeta : Prop :=
∀ (u : ℝ),
  (3 : ℝ) ≤ u →
    ‖riemannZeta ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) (1 / 2 : ℝ) u)‖ ≤
      (611 / 1000 : ℝ) * u ^ (1 / 6 : ℝ) * Real.log u

/--
KLN, Lemma4.1 proof before uniformization (Eqs3.5--3.7,3.14--3.15): k=1,X=T,T>=3e12; exact
T-dependent mean coefficients.
-/
noncomputable def mollifier_mean_square : Prop :=
∀ (T : ℝ),
  (3000000000000 : ℝ) ≤ T →
    ∀ t > (0 : ℝ),
      ∫ (u : ℝ) in (0 : ℝ)..t,
          ‖(fun (X : ℝ) (s : ℂ) =>
                  ∑ n ∈ Finset.Icc (1 : ℕ) ⌊X⌋₊, (↑((ArithmeticFunction.moebius : ℕ → ℤ) n) : ℂ) * (↑n : ℂ) ^ (-s))
                T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) (1 / 2 : ℝ) u)‖ ^
            (2 : ℕ) ≤
        ((fun (T : ℝ) => (6 : ℝ) / Real.pi ^ (2 : ℕ) + (131 / 125 : ℝ) / Real.log T) T * t +
            (fun (T : ℝ) =>
                  Real.pi * √((1 : ℝ) + (2 / 3 : ℝ) * √(6 / 5 : ℝ)) * (31 / 50 : ℝ) / Real.log T +
                      (6 : ℝ) * √((1 : ℝ) + (2 / 3 : ℝ) * √(6 / 5 : ℝ)) / (Real.pi * T) +
                    Real.pi * √((1 : ℝ) + (2 / 3 : ℝ) * √(6 / 5 : ℝ)) * (131 / 125 : ℝ) / (T * Real.log T))
                T *
              T) *
          Real.log T

/--
KLN, Lemma4.5Eq4.13 andLemma3.7Eqs3.17--3.18: beta=2,alpha=.1202 and the actual mollified square
integral.
-/
noncomputable def source_smoothing : Prop :=
∀ (T : ℝ),
  (3000000000000 : ℝ) ≤ T →
    (fun (T σ : ℝ) =>
          ∫ (t : ℝ),
            ‖(fun (T : ℝ) (s : ℂ) =>
                      (s - (1 : ℂ)) / s * Complex.exp ((↑(601 / 5000 : ℝ) : ℂ) * (s / (↑T : ℂ)) ^ (2 : ℕ)))
                    T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ t) *
                  (fun (X : ℝ) (s : ℂ) =>
                      riemannZeta s *
                          (fun (X : ℝ) (s : ℂ) =>
                              ∑ n ∈ Finset.Icc (1 : ℕ) ⌊X⌋₊,
                                (↑((ArithmeticFunction.moebius : ℕ → ℤ) n) : ℂ) * (↑n : ℂ) ^ (-s))
                            X s -
                        (1 : ℂ))
                    T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ t)‖ ^
              (2 : ℕ))
        T (1 / 2 : ℝ) ≤
      (8 : ℝ) * (601 / 5000 : ℝ) * Real.exp ((601 / 5000 : ℝ) / ((2 : ℝ) * T ^ (2 : ℕ))) *
        ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
          (fun (x : ℝ) => x * Real.exp (-(601 / 2500 : ℝ) * x ^ (2 : ℕ))) x *
            (fun (T x : ℝ) =>
                (fun (X σ t : ℝ) =>
                    ∫ (u : ℝ) in (0 : ℝ)..t,
                      ‖(fun (X : ℝ) (s : ℂ) =>
                              riemannZeta s *
                                  (fun (X : ℝ) (s : ℂ) =>
                                      ∑ n ∈ Finset.Icc (1 : ℕ) ⌊X⌋₊,
                                        (↑((ArithmeticFunction.moebius : ℕ → ℤ) n) : ℂ) * (↑n : ℂ) ^ (-s))
                                    X s -
                                (1 : ℂ))
                            X ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ u)‖ ^
                        (2 : ℕ))
                  T (1 / 2 : ℝ) (x * T))
              T x

/--
KLN Eqs3.10--3.11 andLemma4.7 proof Eqs4.19--4.20, before uniformization: X=T,delta=.3599>0;
exact right-moment operands.
-/
noncomputable def source_right_moment : Prop :=
∀ (T : ℝ),
  (3000000000000 : ℝ) ≤ T →
    (fun (T σ : ℝ) =>
          ∫ (t : ℝ),
            ‖(fun (T : ℝ) (s : ℂ) =>
                      (s - (1 : ℂ)) / s * Complex.exp ((↑(601 / 5000 : ℝ) : ℂ) * (s / (↑T : ℂ)) ^ (2 : ℕ)))
                    T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ t) *
                  (fun (X : ℝ) (s : ℂ) =>
                      riemannZeta s *
                          (fun (X : ℝ) (s : ℂ) =>
                              ∑ n ∈ Finset.Icc (1 : ℕ) ⌊X⌋₊,
                                (↑((ArithmeticFunction.moebius : ℕ → ℤ) n) : ℂ) * (↑n : ℂ) ^ (-s))
                            X s -
                        (1 : ℂ))
                    T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ t)‖ ^
              (2 : ℕ))
        T ((fun (delta T : ℝ) => (1 : ℝ) + delta / Real.log T) (3599 / 10000 : ℝ) T) ≤
      (fun (gamma delta T : ℝ) =>
            (8 : ℝ) * (601 / 5000 : ℝ) *
                Real.exp ((2 : ℝ) * (601 / 5000 : ℝ) * (((1 : ℝ) + delta / Real.log T) / T) ^ (2 : ℕ)) *
              (((fun (gamma delta T : ℝ) =>
                        Real.pi * √((1 : ℝ) + (2 / 3 : ℝ) * √(6 / 5 : ℝ)) * (529 / 1000 : ℝ) / ((2 : ℝ) * delta) *
                            ((1 : ℝ) + (2 : ℝ) * delta / Real.log T) ^ (2 : ℕ) *
                          Real.exp ((2 : ℝ) * delta * gamma / Real.log T))
                      gamma delta T +
                    (fun (gamma delta T : ℝ) =>
                              (529 / 1000 : ℝ) / ((5 : ℝ) * delta * Real.exp delta) *
                                    ((1 : ℝ) + delta / Real.log T) ^ (2 : ℕ) *
                                  Real.exp (delta * (gamma - Real.log (5 : ℝ)) / Real.log T) +
                                (121 / 200 : ℝ) * Real.exp ((-2 : ℝ) * delta) / Real.log T ^ (2 : ℕ))
                            gamma delta T *
                          Real.pi *
                        √((1 : ℝ) + (2 / 3 : ℝ) * √(6 / 5 : ℝ)) /
                      T) /
                  ((4 : ℝ) * (601 / 5000 : ℝ)) +
                (fun (gamma delta T : ℝ) =>
                        (529 / 1000 : ℝ) / ((5 : ℝ) * delta * Real.exp delta) *
                              ((1 : ℝ) + delta / Real.log T) ^ (2 : ℕ) *
                            Real.exp (delta * (gamma - Real.log (5 : ℝ)) / Real.log T) +
                          (121 / 200 : ℝ) * Real.exp ((-2 : ℝ) * delta) / Real.log T ^ (2 : ℕ))
                      gamma delta T *
                    √Real.pi /
                  ((8 : ℝ) * (601 / 5000 : ℝ) * √((2 : ℝ) * (601 / 5000 : ℝ)))))
          Real.eulerMascheroniConstant (3599 / 10000 : ℝ) T *
        Real.log T ^ (2 : ℕ)

/--
KLN Lemmas2.3,2.9,4.12--4.14 andFKS2 Theorem2.7 proof/Eq2.16: regular upper/lower edges, with
the separate CHT divisor-sum improvement C8/2. The final FKS density theorem with delta>=1 is
not invoked.
-/
noncomputable def source_rectangle : Prop :=
∀ (sigma : ℝ),
  (3 / 4 : ℝ) ≤ sigma →
    sigma ≤ (7 / 8 : ℝ) →
      ∃ (Etop : Set ℝ),
        Etop.Countable ∧
          ∀ (T : ℝ),
            (3000000000000 : ℝ) ≤ T →
              T ∉ Etop →
                ∃ (Elower : Set ℝ),
                  Elower.Countable ∧
                    ∀ (h : ℝ),
                      (3000000000000 : ℝ) - (1 : ℝ) < h →
                        h < (3000000000000 : ℝ) →
                          h ∉ Elower →
                            IEANTN.zetaN' sigma T - IEANTN.zetaN' sigma h ≤
                              (fun (X sigma sigmap mu C7 C8 T h : ℝ) =>
                                  ((T - h) *
                                        Real.log
                                          ((1 : ℝ) +
                                            ((fun (X σ t : ℝ) =>
                                                    ∫ (u : ℝ) in (0 : ℝ)..t,
                                                      ‖(fun (X : ℝ) (s : ℂ) =>
                                                              riemannZeta s *
                                                                  (fun (X : ℝ) (s : ℂ) =>
                                                                      ∑ n ∈ Finset.Icc (1 : ℕ) ⌊X⌋₊,
                                                                        (↑((ArithmeticFunction.moebius : ℕ → ℤ) n) :
                                                                            ℂ) *
                                                                          (↑n : ℂ) ^ (-s))
                                                                    X s -
                                                                (1 : ℂ))
                                                            X
                                                            ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ u)‖ ^
                                                        (2 : ℕ))
                                                  X sigmap T -
                                                (fun (X σ t : ℝ) =>
                                                    ∫ (u : ℝ) in (0 : ℝ)..t,
                                                      ‖(fun (X : ℝ) (s : ℂ) =>
                                                              riemannZeta s *
                                                                  (fun (X : ℝ) (s : ℂ) =>
                                                                      ∑ n ∈ Finset.Icc (1 : ℕ) ⌊X⌋₊,
                                                                        (↑((ArithmeticFunction.moebius : ℕ → ℤ) n) :
                                                                            ℂ) *
                                                                          (↑n : ℂ) ^ (-s))
                                                                    X s -
                                                                (1 : ℂ))
                                                            X
                                                            ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ u)‖ ^
                                                        (2 : ℕ))
                                                  X sigmap h) /
                                              (T - h)) +
                                      (C7 * (mu - sigmap) + C8 / (2 : ℝ)) * Real.log T) /
                                    ((2 : ℝ) * Real.pi * (sigma - sigmap)))
                                T sigma (sigma - (3681 / 10000 : ℝ) / Real.log T) (1237 / 1000 : ℝ)
                                ((fun (gamma h : ℝ) =>
                                    ((2 : ℝ) * ((1 : ℝ) + (2 : ℝ) * (507 / 2000 : ℝ)) +
                                          (2 : ℝ) * Real.pi * ((1 : ℝ) + (507 / 2000 : ℝ))) /
                                        Real.log (2 : ℝ) +
                                      (fun (gamma h : ℝ) =>
                                            Real.pi / Real.log (2 : ℝ) *
                                                  (Real.log
                                                        (((1 : ℝ) +
                                                            (2 : ℝ) /
                                                              ((1503 / 500 : ℝ) *
                                                                  (fun (s : ℝ) =>
                                                                      ∑' (n : ℕ), ((↑n : ℝ) + (1 : ℝ)) ^ (-s))
                                                                    ((1 : ℝ) + (507 / 2000 : ℝ)) *
                                                                (3000000000000 : ℝ) ^ ((1 : ℝ) + (507 / 2000 : ℝ)))) *
                                                          ((1503 / 500 : ℝ) *
                                                              (fun (s : ℝ) => ∑' (n : ℕ), ((↑n : ℝ) + (1 : ℝ)) ^ (-s))
                                                                ((1 : ℝ) + (507 / 2000 : ℝ))) ^
                                                            (2 : ℕ)) +
                                                      Real.log
                                                        ((fun (s : ℝ) => ∑' (n : ℕ), ((↑n : ℝ) + (1 : ℝ)) ^ (-s))
                                                                ((1 : ℝ) + (507 / 2000 : ℝ)) ^
                                                              (4 : ℕ) /
                                                            (fun (s : ℝ) => ∑' (n : ℕ), ((↑n : ℝ) + (1 : ℝ)) ^ (-s))
                                                                ((2 : ℝ) + (2 : ℝ) * (507 / 2000 : ℝ)) ^
                                                              (2 : ℕ) +
                                                          (2 : ℝ) *
                                                              (fun (s : ℝ) => ∑' (n : ℕ), ((↑n : ℝ) + (1 : ℝ)) ^ (-s))
                                                                  ((1 : ℝ) + (507 / 2000 : ℝ)) ^
                                                                (2 : ℕ) /
                                                            (fun (s : ℝ) => ∑' (n : ℕ), ((↑n : ℝ) + (1 : ℝ)) ^ (-s))
                                                              ((2 : ℝ) + (2 : ℝ) * (507 / 2000 : ℝ))) -
                                                    (2 : ℝ) *
                                                      Real.log
                                                        ((1 : ℝ) -
                                                          (fun (X q gamma : ℝ) =>
                                                                ((1 : ℝ) + q) * Real.log X /
                                                                    (q * Real.exp (q * Real.log X)) *
                                                                  ((1 : ℝ) + (1 : ℝ) / (q * Real.log X) +
                                                                      gamma / Real.log X +
                                                                    (7 : ℝ) * q /
                                                                      ((12 : ℝ) * ((1 : ℝ) + q) * X * Real.log X)))
                                                              (1000000000 : ℝ) (507 / 2000 : ℝ) gamma ^
                                                            (2 : ℕ))) +
                                                Real.pi +
                                              (2 : ℝ) * ((1 : ℝ) + (2 : ℝ) * (507 / 2000 : ℝ)) / Real.log (2 : ℝ) *
                                                Real.log
                                                  ((fun (h : ℝ) =>
                                                        √(((2 : ℝ) + (507 / 2000 : ℝ)) ^ (2 : ℕ) / h ^ (2 : ℕ) +
                                                            (((1 : ℝ) + (2 : ℝ) * (507 / 2000 : ℝ)) / h + (1 : ℝ)) ^
                                                              (2 : ℕ)))
                                                      h /
                                                    ((2 : ℝ) * Real.pi)))
                                          gamma h /
                                        Real.log (3000000000000 : ℝ))
                                  Real.eulerMascheroniConstant h)
                                ((fun (gamma : ℝ) =>
                                    (fun (gamma : ℝ) =>
                                          -Real.log
                                                ((1 : ℝ) -
                                                  (fun (X q gamma : ℝ) =>
                                                        ((1 : ℝ) + q) * Real.log X / (q * Real.exp (q * Real.log X)) *
                                                          ((1 : ℝ) + (1 : ℝ) / (q * Real.log X) + gamma / Real.log X +
                                                            (7 : ℝ) * q / ((12 : ℝ) * ((1 : ℝ) + q) * X * Real.log X)))
                                                      (3000000000000 : ℝ) ((1237 / 1000 : ℝ) - (1 : ℝ)) gamma ^
                                                    (2 : ℕ)) /
                                            (fun (X q gamma : ℝ) =>
                                                  ((1 : ℝ) + q) * Real.log X / (q * Real.exp (q * Real.log X)) *
                                                    ((1 : ℝ) + (1 : ℝ) / (q * Real.log X) + gamma / Real.log X +
                                                      (7 : ℝ) * q / ((12 : ℝ) * ((1 : ℝ) + q) * X * Real.log X)))
                                                (3000000000000 : ℝ) ((1237 / 1000 : ℝ) - (1 : ℝ)) gamma ^
                                              (2 : ℕ))
                                        gamma *
                                      (Real.log (3000000000000 : ℝ) ^ (2 : ℕ) /
                                          Real.exp
                                            (((2 : ℝ) * (1237 / 1000 : ℝ) - (2 : ℝ)) * Real.log (3000000000000 : ℝ)) *
                                        ((4 : ℝ) * (1237 / 1000 : ℝ) *
                                              (fun (tau : ℝ) =>
                                                  (1 : ℝ) + (3 : ℝ) / ((tau - (1 : ℝ)) * Real.log (3000000000000 : ℝ)) +
                                                      (6 : ℝ) /
                                                        ((tau - (1 : ℝ)) * Real.log (3000000000000 : ℝ)) ^ (2 : ℕ) +
                                                    (6 : ℝ) /
                                                      ((tau - (1 : ℝ)) * Real.log (3000000000000 : ℝ)) ^ (3 : ℕ))
                                                ((2 : ℝ) * (1237 / 1000 : ℝ)) /
                                            ((2 : ℝ) * (1237 / 1000 : ℝ) - (1 : ℝ)) +
                                          (2 : ℝ) * Real.pi * √((1 : ℝ) + (2 / 3 : ℝ) * √(6 / 5 : ℝ)) *
                                                ((2 : ℝ) * (1237 / 1000 : ℝ) - (1 : ℝ)) *
                                              (fun (tau : ℝ) =>
                                                  (1 : ℝ) + (3 : ℝ) / ((tau - (1 : ℝ)) * Real.log (3000000000000 : ℝ)) +
                                                      (6 : ℝ) /
                                                        ((tau - (1 : ℝ)) * Real.log (3000000000000 : ℝ)) ^ (2 : ℕ) +
                                                    (6 : ℝ) /
                                                      ((tau - (1 : ℝ)) * Real.log (3000000000000 : ℝ)) ^ (3 : ℕ))
                                                ((2 : ℝ) * (1237 / 1000 : ℝ) - (1 : ℝ)) /
                                            ((1237 / 1000 : ℝ) - (1 : ℝ)))))
                                  Real.eulerMascheroniConstant)
                                T h

/--
KLN, Lemma4.9 proof andEq3.19: actual cumulative-square difference and smoothing minimum,
specialized to d=.3681.
-/
noncomputable def source_unsmoothing : Prop :=
∀ (sigma T : ℝ),
  (3 / 4 : ℝ) ≤ sigma →
    sigma ≤ (7 / 8 : ℝ) →
      (3000000000000 : ℝ) ≤ T →
        (fun (d sigma T : ℝ) =>
              (fun (X σ t : ℝ) =>
                    ∫ (u : ℝ) in (0 : ℝ)..t,
                      ‖(fun (X : ℝ) (s : ℂ) =>
                              riemannZeta s *
                                  (fun (X : ℝ) (s : ℂ) =>
                                      ∑ n ∈ Finset.Icc (1 : ℕ) ⌊X⌋₊,
                                        (↑((ArithmeticFunction.moebius : ℕ → ℤ) n) : ℂ) * (↑n : ℂ) ^ (-s))
                                    X s -
                                (1 : ℂ))
                            X ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ u)‖ ^
                        (2 : ℕ))
                  T ((fun (d sigma T : ℝ) => sigma - d / Real.log T) d sigma T) T -
                (fun (X σ t : ℝ) =>
                    ∫ (u : ℝ) in (0 : ℝ)..t,
                      ‖(fun (X : ℝ) (s : ℂ) =>
                              riemannZeta s *
                                  (fun (X : ℝ) (s : ℂ) =>
                                      ∑ n ∈ Finset.Icc (1 : ℕ) ⌊X⌋₊,
                                        (↑((ArithmeticFunction.moebius : ℕ → ℤ) n) : ℂ) * (↑n : ℂ) ^ (-s))
                                    X s -
                                (1 : ℂ))
                            X ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ u)‖ ^
                        (2 : ℕ))
                  T ((fun (d sigma T : ℝ) => sigma - d / Real.log T) d sigma T) ((3000000000000 : ℝ) - (1 : ℝ)))
            (3681 / 10000 : ℝ) sigma T ≤
          (fun (T σ : ℝ) =>
                ∫ (t : ℝ),
                  ‖(fun (T : ℝ) (s : ℂ) =>
                            (s - (1 : ℂ)) / s * Complex.exp ((↑(601 / 5000 : ℝ) : ℂ) * (s / (↑T : ℂ)) ^ (2 : ℕ)))
                          T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ t) *
                        (fun (X : ℝ) (s : ℂ) =>
                            riemannZeta s *
                                (fun (X : ℝ) (s : ℂ) =>
                                    ∑ n ∈ Finset.Icc (1 : ℕ) ⌊X⌋₊,
                                      (↑((ArithmeticFunction.moebius : ℕ → ℤ) n) : ℂ) * (↑n : ℂ) ^ (-s))
                                  X s -
                              (1 : ℂ))
                          T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ t)‖ ^
                    (2 : ℕ))
              T ((fun (d sigma T : ℝ) => sigma - d / Real.log T) (3681 / 10000 : ℝ) sigma T) /
            ((2 : ℝ) *
              (fun (d sigma T : ℝ) =>
                    ((1 : ℝ) - (1 : ℝ) / ((3000000000000 : ℝ) - (1 : ℝ))) *
                      Real.exp
                        ((601 / 5000 : ℝ) * ((fun (d sigma T : ℝ) => sigma - d / Real.log T) d sigma T / T) ^ (2 : ℕ) -
                          (601 / 5000 : ℝ)))
                  (3681 / 10000 : ℝ) sigma T ^
                (2 : ℕ))

/--
KLN, Lemma4.4Eq4.12: actual smoothed moments on the critical and right lines, specialized to
d=.3681 anddelta=.3599.
-/
noncomputable def source_interpolation : Prop :=
∀ (sigma T : ℝ),
  (3 / 4 : ℝ) ≤ sigma →
    sigma ≤ (7 / 8 : ℝ) →
      (3000000000000 : ℝ) ≤ T →
        (fun (T σ : ℝ) =>
              ∫ (t : ℝ),
                ‖(fun (T : ℝ) (s : ℂ) =>
                          (s - (1 : ℂ)) / s * Complex.exp ((↑(601 / 5000 : ℝ) : ℂ) * (s / (↑T : ℂ)) ^ (2 : ℕ)))
                        T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ t) *
                      (fun (X : ℝ) (s : ℂ) =>
                          riemannZeta s *
                              (fun (X : ℝ) (s : ℂ) =>
                                  ∑ n ∈ Finset.Icc (1 : ℕ) ⌊X⌋₊,
                                    (↑((ArithmeticFunction.moebius : ℕ → ℤ) n) : ℂ) * (↑n : ℂ) ^ (-s))
                                X s -
                            (1 : ℂ))
                        T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ t)‖ ^
                  (2 : ℕ))
            T ((fun (d sigma T : ℝ) => sigma - d / Real.log T) (3681 / 10000 : ℝ) sigma T) ≤
          (fun (T σ : ℝ) =>
                  ∫ (t : ℝ),
                    ‖(fun (T : ℝ) (s : ℂ) =>
                              (s - (1 : ℂ)) / s * Complex.exp ((↑(601 / 5000 : ℝ) : ℂ) * (s / (↑T : ℂ)) ^ (2 : ℕ)))
                            T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ t) *
                          (fun (X : ℝ) (s : ℂ) =>
                              riemannZeta s *
                                  (fun (X : ℝ) (s : ℂ) =>
                                      ∑ n ∈ Finset.Icc (1 : ℕ) ⌊X⌋₊,
                                        (↑((ArithmeticFunction.moebius : ℕ → ℤ) n) : ℂ) * (↑n : ℂ) ^ (-s))
                                    X s -
                                (1 : ℂ))
                            T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ t)‖ ^
                      (2 : ℕ))
                T (1 / 2 : ℝ) ^
              (((fun (delta T : ℝ) => (1 : ℝ) + delta / Real.log T) (3599 / 10000 : ℝ) T -
                  (fun (d sigma T : ℝ) => sigma - d / Real.log T) (3681 / 10000 : ℝ) sigma T) /
                ((fun (delta T : ℝ) => (1 : ℝ) + delta / Real.log T) (3599 / 10000 : ℝ) T - (1 / 2 : ℝ))) *
            (fun (T σ : ℝ) =>
                  ∫ (t : ℝ),
                    ‖(fun (T : ℝ) (s : ℂ) =>
                              (s - (1 : ℂ)) / s * Complex.exp ((↑(601 / 5000 : ℝ) : ℂ) * (s / (↑T : ℂ)) ^ (2 : ℕ)))
                            T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ t) *
                          (fun (X : ℝ) (s : ℂ) =>
                              riemannZeta s *
                                  (fun (X : ℝ) (s : ℂ) =>
                                      ∑ n ∈ Finset.Icc (1 : ℕ) ⌊X⌋₊,
                                        (↑((ArithmeticFunction.moebius : ℕ → ℤ) n) : ℂ) * (↑n : ℂ) ^ (-s))
                                    X s -
                                (1 : ℂ))
                            T ((fun (σ t : ℝ) => (↑σ : ℂ) + (↑t : ℂ) * Complex.I) σ t)‖ ^
                      (2 : ℕ))
                T ((fun (delta T : ℝ) => (1 : ℝ) + delta / Real.log T) (3599 / 10000 : ℝ) T) ^
              (((fun (d sigma T : ℝ) => sigma - d / Real.log T) (3681 / 10000 : ℝ) sigma T - (1 / 2 : ℝ)) /
                ((fun (delta T : ℝ) => (1 : ℝ) + delta / Real.log T) (3599 / 10000 : ℝ) T - (1 / 2 : ℝ)))

/--
Cully-Hugill--Johnston (arXiv2111.10001v5), Theorem1.2Eq1.5 andTable4 firstrow, PDFpage20:
M=6.431,log(x_M)=40,alpha=1/2; strict height window retained.
-/
noncomputable def original_chj : Prop :=
∀ (x T : ℝ),
  Real.exp (40 : ℝ) ≤ x →
    Max.max (51 : ℝ) (Real.log x) < T →
      T < (√x - (2 : ℝ)) / (2 : ℝ) →
        |Chebyshev.psi x - x +
              (IEANTN.zetaZeroesSum (Set.Ioo (0 : ℝ) (1 : ℝ)) (Set.Icc (-T) T) fun (rho : ℂ) =>
                  (↑x : ℂ) ^ rho / rho).re| ≤
          (6431 / 1000 : ℝ) * x * Real.log x / T

end
end MomentSourceInputs.v1
