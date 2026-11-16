/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PowerError

namespace MomentPNT.v1
open IEANTN Real

/-- Source-first mass/first-moment route, normalized by Li_2, on the entire stated ray. -/
def moment_pi : Prop :=
  HasPowerLogBound Eπ (8848544 / 1000000000) 0 (7 / 8) (exp 300)

/-- The same pair of source-derived statistics also bounds the Chebyshev error. -/
def moment_psi : Prop :=
  HasPowerLogBound Eψ (8848544 / 1000000000) 0 (7 / 8) (exp 300)

/-- Stronger same-premise ordinary-kernel direct-vector control; this is not source-first PV. -/
def kernel_control_pi : Prop :=
  HasPowerLogBound Eπ (8732871 / 1000000000) 0 (7 / 8) (exp 300)

/-- The direct-vector control also bounds the Chebyshev error, with the same fourteen inputs. -/
def kernel_control_psi : Prop :=
  HasPowerLogBound Eψ (8732871 / 1000000000) 0 (7 / 8) (exp 300)

/-- Reusable whole-ray profile supplied by the same two source-program outputs.
Every logarithmic onset L >= 330 is allowed; finite RH remains fixed at 3e12. -/
def moment_future_pi : Prop :=
  ∀ L : ℝ, 330 ≤ L → HasPowerLogBound Eπ
    ((1 + 1 / 1000000000) *
      (1 / 1000000000000 +
       L * ((L - 240) * (6330434505 / 1000000000000) +
          520404202477 / 1000000000000) / ((L - 77) * (L - 163)) +
       ((1 / 250000) * L / (L - 160) + 1 / 50000000 +
        (1 / 1000000000000) * L / (L - 880 / 3) + 1 / 1000000000000)) +
     1 / 1000000000000 + 1 / 100000000) 0 (7 / 8) (exp L)

/-- For every x >= exp330, the same fixed-width interval contains this
many primes. It is a consequence of the reusable moment profile, not another
independent numerical discovery. The interval is open at x and closed at its right end. -/
def moment_prime_rich : Prop :=
  ∀ x : ℝ, exp 330 ≤ x →
    (95363 / 100000000 : ℝ) * x ^ ((7 : ℝ) / 8) / log x ≤
      primeCounting (x + (9 / 500 : ℝ) * x ^ ((7 : ℝ) / 8)) - primeCounting x

end MomentPNT.v1
