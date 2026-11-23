# Supplemental Box analysis

This work is separate from the immutable primary454-module capture.
`BoxFourierSeries.lean` proves the complete uniformly convergent Fourier series
of the actual absolute sine, its one-sided cosine form and the nonnegative
(1 minus cosine) form. `BoxPositiveMellin.lean` uses that identity to prove a
justified infinite series/integral exchange for the actual Mellin function
throughout0<s<1. Both compile with only the standard three axioms.

`BoxCDFConstruction.lean` gives an exact finite Mangoldt representation of the
actual averaged psi function. It exhibits a positive argument below1 where
the cumulative box weight is1, identifying why that raw weight cannot be
passed directly to Green's support-restricted formula. A smooth lower cutoff
may preserve integer Mangoldt values; its Mellin/zero/trivial correction must
still be proved. This is not an impossibility claim about the Box formula.

The full Box explicit formula, Box zero estimate and the two numerical Mellin
identities remain open. These new results discharge genuine analytic substeps;
they do not assume or claim those four final predicates. All new work here is
ordinary kernel mathematics, not source-first PV. The older C model's exact
rendered-source identity still carries an explicit renderer/model contract;
independent parser soundness is not established by this campaign.
