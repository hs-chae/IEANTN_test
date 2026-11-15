# FixedL=300 vector challenger: ordinary kernel verification

This independently verifies the complete768-vector rational upper bound for the
actual paired factor. It reuses already-kernel-proved mass-cell intervals and
exact D words, then checks all768 interval arithmetic terms and prefix sums.
The negative exponential correction is dropped by a proved sign inequality; it
is not numerically evaluated. No parameter search or claim of optimality.

The unchanged fourteen analytic inputs yield BOTH Epi,Epsi≤0.008732871*x^(-1/8)
for every x≥exp300. This is strictly stronger than the two-moment source-program
coefficient0.008848544. It is kernel-only checking, NOT source-first PV. No C
execution proof modules or native execution axioms are imported. The new campaign
numerical evidence is charged; this is not original P0 or a free analytic gift.

Exact parameters were locked before execution: L300,768cells,128fixed-point bits,
512-bit words, no seed. A single ceil-to1e-9 rounding rule chose the coefficient.
Model6 +numerical4 +fullANT7 roots compile with complete Std3 closures. The first
Model draft only referenced an absent extensionality helper; it was rejected,
preserved and replaced by the generic constructor proof, without changing inputs.

Use the same pinned public Lean4.34.0-rc2/Mathlib71a80585 environment as the base.
Actual reproduction is explicitly CHAINED565+3: only the precise independently
accepted565 source-built bank may seed it, after full source/command/object/log/
typed-root association before and after. Actual new sources compile afresh.

    python3 -B reproduce.py --environment /absolute/environment.json \
      --base-run /absolute/accepted565/run --out /absolute/fresh-run

Without --base-run, the enclosed base/reproduce.py first regenerates all numerical
proposals and compiles all565 application sources in an empty bank, before the
three-source continuation. This is the complete clean-environment route, typically
about25minutes with128GiB/16CPU/jobs8 for the base on the current machine.
The three-source append is bounded32GiB/4CPU/600s. Namespace isolation and measured
resource acceptance have separate receipts. Accepted proof objects are preserved.

    python3 -OO -B reproduce.py --out /absolute/new-check --check-inputs-only

That route checks exact sources and actually regenerates the full new Data.lean
proposal from locked base numerical data, but does not claim proof replay.
All active checks reject malformed/duplicate/nonfinite/overflow JSON in0/O/OO.
Missing audit roots fail before axiom collection; actual types and complete
closures are checked. Every generated proposal is mathematically untrusted until
the later exactkernel proofs and complete ANT consumer pass.
